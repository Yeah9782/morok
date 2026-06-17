#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
#
# Virtualization differential gate.  Like differential.sh, but in addition to
# requiring identical clean-vs-obfuscated output it asserts that the bytecode
# virtualizer actually fired (a `morok.vm.bytecode.*` global was emitted) — so a
# regression that silently stops lifting (the exact failure that motivated the
# multi-block expansion) fails the gate instead of trivially passing.
#
# Usage: differential_vm.sh <clang> <plugin> <sdk> <source> <config.toml> [seed]
set -euo pipefail

CLANG="$1"; PLUGIN="$2"; SDK="$3"; SRC="$4"; CONFIG="$5"; SEED="${6:-4242}"

if [ -z "$SDK" ] && command -v xcrun >/dev/null 2>&1; then
  SDK="$(xcrun --show-sdk-path 2>/dev/null || true)"
fi
SYSROOT=()
[ -n "$SDK" ] && SYSROOT=(-isysroot "$SDK")

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

"$CLANG" "${SYSROOT[@]}" -O2 "$SRC" -o "$TMP/ref"
"$CLANG" "${SYSROOT[@]}" -O2 \
    -fpass-plugin="$PLUGIN" \
    -mllvm -morok -mllvm -morok-config="$CONFIG" -mllvm -morok-seed="$SEED" \
    "$SRC" -o "$TMP/obf"
"$CLANG" "${SYSROOT[@]}" -O2 \
    -fpass-plugin="$PLUGIN" \
    -mllvm -morok -mllvm -morok-config="$CONFIG" -mllvm -morok-seed="$SEED" \
    -S -emit-llvm "$SRC" -o "$TMP/obf.ll"

LIFTED="$(grep -c '@morok\.vm\.bytecode\.' "$TMP/obf.ll" || true)"
if [ "$LIFTED" -eq 0 ]; then
  echo "FAIL config=$CONFIG seed=$SEED  the VM lifted no functions (no morok.vm.bytecode.*)" >&2
  exit 1
fi

REF="$("$TMP/ref")"
OBF="$("$TMP/obf")"
if [ "$REF" != "$OBF" ]; then
  echo "FAIL config=$CONFIG seed=$SEED  ref='$REF'  obf='$OBF'" >&2
  exit 1
fi
echo "OK   config=$CONFIG seed=$SEED  lifted>=1  output=$REF"
exit 0
