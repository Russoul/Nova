#!/usr/bin/env bash
# Checks that every src/nova/*.nova module elaborates with zero
# obligations.
#
# By default this is ONE run over src/nova/all.nova, which imports every
# module: the loader deduplicates by module name, so a shared dependency
# elaborates once instead of once per importer. That is sound because
# the lemma store is scoped to a module's import closure — a module
# elaborates inside all.nova exactly as it does standalone.
#
#   --per-file   elaborate each module separately as well (the old
#                behaviour; ~5x slower, and the only way to catch a
#                module that all.nova forgot to list)
set -u
cd "$(dirname "$0")"

pack build nova.ipkg >/dev/null || exit 1

APP="build/exec/nova"
ALL="src/nova/all.nova"

# all.nova must list every module, or the fast path would silently skip
# one
missing=0
for file in src/nova/*.nova; do
  name="$(basename "$file" .nova)"
  [ "$name" = "all" ] && continue
  if ! grep -q "^import ${name}\$" "$ALL"; then
    echo "FAIL: $name is not imported by $ALL"
    missing=$((missing + 1))
  fi
done
if [ "$missing" -gt 0 ]; then
  echo "$ALL is out of date — add the missing imports"
  exit 1
fi

if [ "${1:-}" = "--per-file" ]; then
  pass=0
  fail=0
  for file in src/nova/*.nova; do
    name="$(basename "$file" .nova)"
    [ "$name" = "all" ] && continue
    if output="$("$APP" elab "$file" 2>&1)"; then
      pass=$((pass + 1))
    else
      fail=$((fail + 1))
      echo "FAIL: $name"
      echo "$output" | sed 's/^/  /'
    fi
  done
  total=$((pass + fail))
  echo "$pass/$total elaborations passed (per-file)"
  [ "$fail" -eq 0 ] || exit 1
fi

count="$(grep -c '^import ' "$ALL")"
if output="$("$APP" elab "$ALL" 2>&1)"; then
  echo "$count/$count elaborations passed"
else
  echo "FAIL: $ALL"
  echo "$output" | sed 's/^/  /'
  exit 1
fi

# ... and again under the SEARCHLESS default (SearchlessElaboration.md
# §5.3): every item without a `using` clause discharges with hypotheses
# and computation only, so this run proves the corpus's store use is
# fully NAMED — acceptance is a function of the file, not the store
if output="$(NOVA_SCOPED=1 "$APP" elab "$ALL" 2>&1)"; then
  echo "$count/$count elaborations passed (scoped)"
else
  echo "FAIL (scoped): $ALL"
  echo "$output" | sed 's/^/  /'
  exit 1
fi
