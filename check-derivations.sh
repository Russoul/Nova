#!/usr/bin/env bash
# Checks that every (session.rules, session.target) pair under derivations/
# is trivially derivable: walking session.rules builds a Truth table with
# `generate`, and every judgement listed in session.target must already be
# present in it (`check`). Mirrors what `nova-foundation-app check` does.
set -u
cd "$(dirname "$0")"

pack build nova-foundation.ipkg >/dev/null || exit 1

APP="build/exec/nova-foundation-app"

pass=0
fail=0

for dir in derivations/*/; do
  name="$(basename "$dir")"
  rules="${dir}session.rules"
  target="${dir}session.target"
  [ -f "$rules" ] && [ -f "$target" ] || continue

  output="$("$APP" check "$rules" "$target")"
  if [ "$output" = "Ok" ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    echo "FAIL: $name"
    echo "$output" | sed 's/^/  /'
  fi
done

total=$((pass + fail))
echo "$pass/$total derivations passed"

[ "$fail" -eq 0 ]
