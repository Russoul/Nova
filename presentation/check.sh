#!/usr/bin/env bash
# Verifies the presentation material against the elaborator:
#   * every finished file (*.nova here) is ACCEPTED;
#   * every live starting point (start/*.nova) elaborates with open
#     holes/obligations but NO failed items.
# Usage: ./check.sh  (from presentation/; NOVA_BIN overrides the executable)
set -u
cd "$(dirname "$0")"
NOVA="${NOVA_BIN:-../build/exec/nova}"
status=0
for f in Arith Vect Equality Bag Stream; do
  if "$NOVA" elab "$f.nova" 2>&1 | grep -q '^Accepted\.$'; then
    echo "ok       $f.nova"
  else
    echo "FAILED   $f.nova"; status=1
  fi
done
for f in start/*.nova; do
  out="$("$NOVA" elab "$f" 2>&1)"
  if echo "$out" | grep -q 'failed to elaborate\|error:'; then
    echo "FAILED   $f (an item failed — a start file may only have holes/obligations)"; status=1
  else
    holes=$(echo "$out" | grep -c '^  \[?')
    obls=$(echo "$out" | grep -c '^  \[[0-9]')
    echo "ok       $f (holes: $holes, obligations: $obls)"
  fi
done
exit $status
