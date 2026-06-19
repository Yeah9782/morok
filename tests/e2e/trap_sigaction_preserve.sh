#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
#
# Darwin regression for TrapOracle's temporary SIGTRAP disposition.  A dependent
# dylib installs an SA_SIGINFO handler before executable constructors run; the
# protected executable must observe the full disposition after Morok's ctor.
#
# Usage: trap_sigaction_preserve.sh <clang> <plugin> <sdk> <source> <config.toml> [seed]
set -euo pipefail

CLANG="$1"
PLUGIN="$2"
SDK="$3"
SRC="$4"
CONFIG="$5"
SEED="${6:-8863}"

if [ "$(uname -s)" != "Darwin" ]; then
  echo "SKIP trap sigaction preservation requires Darwin"
  exit 77
fi

if [ -z "$SDK" ] && command -v xcrun >/dev/null 2>&1; then
  SDK="$(xcrun --show-sdk-path 2>/dev/null || true)"
fi

SYSROOT=()
[ -n "$SDK" ] && SYSROOT=(-isysroot "$SDK")

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

CFLAGS=(-O2 -std=c11 -D_DARWIN_C_SOURCE -fno-builtin)
LIB="$TMP/libtrap_preinstall.dylib"

"$CLANG" "${SYSROOT[@]}" "${CFLAGS[@]}" -DMOROK_TRAP_SUPPORT \
  -dynamiclib "$SRC" -o "$LIB"

LINK=(-L"$TMP" -ltrap_preinstall "-Wl,-rpath,$TMP")

"$CLANG" "${SYSROOT[@]}" "${CFLAGS[@]}" "$SRC" "${LINK[@]}" -o "$TMP/ref"

env MOROK_ENABLE=1 MOROK_CONFIG="$CONFIG" MOROK_SEED="$SEED" \
  "$CLANG" "${SYSROOT[@]}" "${CFLAGS[@]}" -fpass-plugin="$PLUGIN" \
  "$SRC" "${LINK[@]}" -o "$TMP/obf"

REF="$(DYLD_LIBRARY_PATH="$TMP" "$TMP/ref")"
OBF="$(DYLD_LIBRARY_PATH="$TMP" "$TMP/obf")"

if [ "$REF" != "$OBF" ]; then
  echo "FAIL ref='$REF' obf='$OBF'" >&2
  exit 1
fi

echo "OK trap sigaction preserved output=$OBF"
