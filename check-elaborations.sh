#!/usr/bin/env bash
# Elaborates every src/nova/*.nova surface file; each must be
# accepted (elaborate with zero obligations).
set -u
cd "$(dirname "$0")"

pack build nova.ipkg >/dev/null || exit 1

APP="build/exec/nova"

pass=0
fail=0

for file in src/nova/*.nova; do
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
