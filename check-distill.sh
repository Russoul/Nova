#!/usr/bin/env bash
# The corpus round-trip gate of docs/NovaPerfectSurface.txt: distill
# the whole corpus and verify — re-parsed ASTs structurally identical,
# re-elaboration identical, both runs accepted — AND enforce that
# src/nova is in CANONICAL DISTILL FORM: distilling it must reproduce
# it byte for byte (the corpus was rewritten into this form; edits
# that leave canonical form are re-normalized by
#   build/exec/nova distill src/nova/all.nova <tmp> && cp <tmp>/*.nova src/nova/ ).
#
# NOVA_BIN=<path>  use that `nova` instead of building one with pack.
set -e
if [ -n "${NOVA_BIN:-}" ]; then
  NOVA="$NOVA_BIN"
else
  pack build nova.ipkg
  NOVA="build/exec/nova"
fi
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
"$NOVA" distill src/nova/all.nova "$tmp"
fail=0
for f in "$tmp"/*.nova; do
  if ! diff -q "$f" "src/nova/$(basename "$f")" > /dev/null; then
    echo "not in canonical distill form: src/nova/$(basename "$f")"
    fail=1
  fi
done
if [ "$fail" -ne 0 ]; then
  echo "check-distill: FAILED — re-normalize with 'nova distill' (see header)"
  exit 1
fi
echo "check-distill: corpus round-trip OK, canonical form verified"
