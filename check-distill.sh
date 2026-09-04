#!/usr/bin/env bash
# The corpus round-trip gate of docs/NovaPerfectSurface.txt: distill
# the whole corpus and verify — re-parsed ASTs structurally identical,
# re-elaboration identical, both runs accepted — AND enforce that
# src/nova is in CANONICAL DISTILL FORM: distilling it must reproduce
# it byte for byte (the corpus was rewritten into this form; edits
# that leave canonical form are re-normalized by ./normalize-corpus.sh,
# or `make normalize` — this gate's fix half).
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
# the corpus is a TREE, and distill mirrors it under $tmp (a module's
# path IS its dotted name — Nova.Elaboration.Loader.modPath), so
# compare by path RELATIVE to each root, not by basename: Int/order,
# Rat/order and Real/order share one.
fail=0
while IFS= read -r f; do
  rel="${f#"$tmp"/}"
  if ! diff -q "$f" "src/nova/$rel" > /dev/null; then
    echo "not in canonical distill form: src/nova/$rel"
    fail=1
  fi
done < <(find "$tmp" -name '*.nova' | LC_ALL=C sort)
if [ "$fail" -ne 0 ]; then
  echo "check-distill: FAILED — run ./normalize-corpus.sh to fix"
  exit 1
fi
echo "check-distill: corpus round-trip OK, canonical form verified"
