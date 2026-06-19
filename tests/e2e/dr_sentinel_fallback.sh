#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
#
# Linux x86_64 regression for #49: if the DR sentinel cannot fork at startup,
# the protected process must keep the ptrace self-trace fallback active.
#
# Usage: dr_sentinel_fallback.sh <clang> <plugin> <sdk> <source> <config.toml> [seed]
set -euo pipefail

CLANG="$1"
PLUGIN="$2"
SDK="$3"
SRC="$4"
CONFIG="$5"
SEED="${6:-4949}"

if [ "$(uname -s)" != "Linux" ] || [ "$(uname -m)" != "x86_64" ]; then
  echo "SKIP DR sentinel fallback requires Linux x86_64"
  exit 77
fi

SYSROOT=()
[ -n "$SDK" ] && SYSROOT=(-isysroot "$SDK")

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

CFLAGS=(-O2 -std=c11 -D_GNU_SOURCE -fno-builtin)

"$CLANG" "${SYSROOT[@]}" "${CFLAGS[@]}" "$SRC" -o "$TMP/ref"

cat >"$TMP/fork_probe.c" <<'EOF'
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>

int main(void) {
  struct rlimit rl;
  rl.rlim_cur = 1;
  rl.rlim_max = 1;
  if (setrlimit(RLIMIT_NPROC, &rl) != 0)
    return 77;
  pid_t pid = fork();
  if (pid < 0)
    return 0;
  if (pid == 0)
    _exit(0);
  (void)waitpid(pid, 0, 0);
  return 1;
}
EOF
"$CLANG" "${SYSROOT[@]}" -O2 "$TMP/fork_probe.c" -o "$TMP/fork_probe"

set +e
"$TMP/fork_probe"
probe_rc=$?
set -e
case "$probe_rc" in
  0) ;;
  1)
    echo "SKIP RLIMIT_NPROC did not force fork failure on this host"
    exit 77
    ;;
  77)
    echo "SKIP cannot lower RLIMIT_NPROC on this host"
    exit 77
    ;;
  *)
    echo "FAIL fork probe exited with $probe_rc" >&2
    exit 1
    ;;
esac

ref_out="$("$TMP/ref")"
if [ "$ref_out" != "tracer=0" ]; then
  echo "FAIL clean fixture unexpectedly traced: '$ref_out'" >&2
  exit 1
fi

env MOROK_ENABLE=1 MOROK_CONFIG="$CONFIG" MOROK_SEED="$SEED" \
  "$CLANG" "${SYSROOT[@]}" "${CFLAGS[@]}" -fpass-plugin="$PLUGIN" \
  "$SRC" -o "$TMP/obf"

set +e
obf_out="$(ulimit -u 1 2>/dev/null || exit 77; exec "$TMP/obf")"
obf_rc=$?
set -e
if [ "$obf_rc" -eq 77 ]; then
  echo "SKIP cannot apply low process limit to protected binary"
  exit 77
fi
if [ "$obf_rc" -ne 0 ]; then
  echo "FAIL protected binary exited with $obf_rc output='$obf_out'" >&2
  exit 1
fi
if [ "$obf_out" != "tracer=1" ]; then
  echo "FAIL expected runtime self-trace fallback, got '$obf_out'" >&2
  exit 1
fi

echo "OK DR sentinel fallback output=$obf_out"
