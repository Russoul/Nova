#!/usr/bin/env bash
# Rewrites src/nova into CANONICAL DISTILL FORM — the fix to
# check-distill.sh's gate (docs/NovaPerfectSurface.txt, the round-trip
# contract). Run it after editing the corpus, or after any change to the
# grammar or the printer that moves how a term is spelled.
#
# This is safe by construction: `nova distill` elaborates the closure,
# requires acceptance, re-parses its own output and requires structurally
# identical ASTs, then re-elaborates and requires an identical run. Only
# if all of that passes does anything get copied back — a corpus that
# does not elaborate, or a printer that does not round-trip, aborts here
# with nothing written.
#
# Only files that actually differ are rewritten, so a no-op run leaves
# every mtime alone and prints "already canonical".
#
# NOVA_BIN=<path>  use that `nova` instead of building one with pack.
set -eu
cd "$(dirname "$0")"

if [ -n "${NOVA_BIN:-}" ]; then
  NOVA="$NOVA_BIN"
else
  pack build nova.ipkg
  NOVA="build/exec/nova"
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

"$NOVA" distill src/nova/all.nova "$tmp"

# A corpus module missing from all.nova's import closure is never
# distilled — and, for the same reason, never checked by
# check-distill.sh. Name them rather than silently leaving them behind
# (check-elaborations.sh --per-file exists for the same blind spot).
# paths are compared RELATIVE to each root: the corpus is a tree, and
# distill mirrors it under $tmp, so a basename is not unique
missing=0
while IFS= read -r f; do
  rel="${f#src/nova/}"
  if [ ! -e "$tmp/$rel" ]; then
    echo "warning: $f is not in all.nova's import closure — not normalized, and not covered by check-distill.sh"
    missing=1
  fi
done < <(find src/nova -name '*.nova' | LC_ALL=C sort)

changed=0
while IFS= read -r f; do
  rel="${f#"$tmp"/}"
  target="src/nova/$rel"
  if ! diff -q "$f" "$target" > /dev/null 2>&1; then
    mkdir -p "$(dirname "$target")"
    cp "$f" "$target"
    echo "  normalized $target"
    changed=$((changed + 1))
  fi
done < <(find "$tmp" -name '*.nova' | LC_ALL=C sort)

if [ "$changed" -eq 0 ]; then
  echo "normalize-corpus: already canonical, nothing rewritten"
else
  echo "normalize-corpus: rewrote $changed file(s) — re-run ./check-distill.sh and the test suite"
fi
[ "$missing" -eq 0 ] || echo "normalize-corpus: some modules were skipped (see warnings above)"
