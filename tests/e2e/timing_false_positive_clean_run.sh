#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
#
# Regression for #18: host/jitter-sensitive timing probes may record telemetry
# under a stretched clock, but they must not dirty the consumed anti-debug seal.

set -uo pipefail

CLANG="$1"
PLUGIN="$2"
SDK="$3"
SRC="$4"
CFG="$5"
SEED="${6:-1818}"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

if [ -z "$SDK" ] && command -v xcrun >/dev/null 2>&1; then
  SDK="$(xcrun --show-sdk-path 2>/dev/null || true)"
fi

SYSROOT=()
[ -n "$SDK" ] && SYSROOT=(-isysroot "$SDK")

COMMON=(-O0 -std=c11 -D_GNU_SOURCE "${SYSROOT[@]}" "$SRC")
MOROK_ENV=(MOROK_ENABLE=1 MOROK_CONFIG="$CFG" MOROK_SEED="$SEED")

if ! "$CLANG" "${COMMON[@]}" -o "$TMP/clean" >/dev/null 2>&1; then
  echo "FAIL clean compile" >&2
  exit 1
fi

if ! env "${MOROK_ENV[@]}" "$CLANG" "${COMMON[@]}" \
      -fpass-plugin="$PLUGIN" -o "$TMP/obf" >/dev/null 2>&1; then
  echo "FAIL obfuscated compile" >&2
  exit 1
fi

if ! env "${MOROK_ENV[@]}" "$CLANG" "${COMMON[@]}" \
      -fpass-plugin="$PLUGIN" -S -emit-llvm -o "$TMP/obf.ll" >/dev/null 2>&1; then
  echo "FAIL obfuscated IR emit" >&2
  exit 1
fi

extract_fn() {
  local fn="$1"
  awk -v fn="$fn" '
    $0 ~ ("define .*@\"?" fn "\"?\\(") { printing = 1 }
    printing { print }
    printing && $0 ~ /^}/ { exit }
  ' "$TMP/obf.ll"
}

for fn in morok.timing.oracle morok.cachetime.oracle morok.microcanary.oracle; do
  body="$(extract_fn "$fn")"
  if [ -z "$body" ]; then
    echo "FAIL missing oracle $fn" >&2
    exit 1
  fi
  if printf '%s\n' "$body" | grep -q 'morok\.seal\.fold\.anti_debug'; then
    echo "FAIL $fn folds a jitter-sensitive verdict into anti_debug seal" >&2
    exit 1
  fi
done

clean_out="$("$TMP/clean" 2>&1)"
clean_rc=$?
obf_out="$("$TMP/obf" 2>&1)"
obf_rc=$?

if [ "$clean_rc" -ne 0 ] || [ "$obf_rc" -ne 0 ]; then
  echo "FAIL runtime exit clean=$clean_rc obf=$obf_rc" >&2
  printf 'clean: %s\nobf: %s\n' "$clean_out" "$obf_out" >&2
  exit 1
fi

if [ "$clean_out" != "$obf_out" ]; then
  echo "FAIL runtime output mismatch" >&2
  printf 'clean: %s\nobf: %s\n' "$clean_out" "$obf_out" >&2
  exit 1
fi

echo "OK timing false-positive clean run preserved: $obf_out"
