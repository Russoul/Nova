#!/usr/bin/env bash
# Elaborates every elaborations/*.nova surface file; each must be
# accepted (elaborate with zero obligations).
set -u
cd "$(dirname "$0")"

pack build nova-foundation.ipkg >/dev/null || exit 1

APP="build/exec/nova-foundation-app"

pass=0
fail=0

for file in elaborations/*.nova; do
  name="$(basename "$file" .nova)"
  if output="$("$APP" elab "$file" 2>&1)"; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    echo "FAIL: $name"
    echo "$output" | sed 's/^/  /'
  fi
done

total=$((pass + fail))
echo "$pass/$total elaborations passed"

[ "$fail" -eq 0 ]
