#!/usr/bin/env bash
# Golden tests of the kernel: every CASE.nk in DIR is checked with the
# nova binary and its output (stdout, then "exit N") compared with
# CASE.expected. --promote rewrites the expected files instead.
#   run.sh NOVA [--promote] DIR
set -u
nova=$1; shift
promote=0
if [ "${1:-}" = --promote ]; then promote=1; shift; fi
dir=$1
fail=0
for f in "$dir"/*.nk; do
  exp="${f%.nk}.expected"
  out=$("$nova" check "$f" 2>&1; echo "exit $?")
  if [ $promote = 1 ]; then
    printf '%s\n' "$out" > "$exp"
    echo "promoted $exp"
    continue
  fi
  if [ ! -f "$exp" ]; then
    echo "MISSING $exp"; fail=1; continue
  fi
  if ! diff -u "$exp" <(printf '%s\n' "$out"); then
    echo "FAIL $f"; fail=1
  fi
done
# NAME-inline.nk and NAME-block.nk spell the same items two ways: their
# outputs must coincide.
for b in "$dir"/*-block.nk; do
  [ -e "$b" ] || continue
  i="${b%-block.nk}-inline.nk"
  [ -f "$i" ] || continue
  if ! diff -u <("$nova" check "$i" 2>&1) <("$nova" check "$b" 2>&1); then
    echo "FAIL $i and $b differ"; fail=1
  fi
done
exit $fail
