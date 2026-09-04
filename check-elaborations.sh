#!/usr/bin/env bash
# Checks that every module under src/nova/ elaborates with zero
# obligations. The corpus is a TREE: a module's name is its path from
# src/nova with '/' turned into '.' (src/nova/Real/mul.nova is the
# module Real.mul), which is exactly how the loader resolves it against
# the nova.root marker.
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
#
# NOVA_BIN=<path>  use that `nova` instead of building one with pack.
set -u
cd "$(dirname "$0")"

# NOVA_BIN names an already-built `nova`; without it, build one with pack.
if [ -n "${NOVA_BIN:-}" ]; then
  APP="$NOVA_BIN"
else
  pack build nova.ipkg >/dev/null || exit 1
  APP="build/exec/nova"
fi

ALL="src/nova/all.nova"

# every corpus module, as a dotted module name (src/nova/Real/mul.nova
# ⇝ Real.mul), all.nova itself excluded
modules() {
  find src/nova -name '*.nova' ! -name all.nova \
    | sed -e 's|^src/nova/||' -e 's|\.nova$||' -e 's|/|.|g' \
    | LC_ALL=C sort
}

# all.nova must list every module, or the fast path would silently skip
# one
missing=0
while IFS= read -r name; do
  if ! grep -q "^import ${name}\$" "$ALL"; then
    echo "FAIL: $name is not imported by $ALL"
    missing=$((missing + 1))
  fi
done < <(modules)
if [ "$missing" -gt 0 ]; then
  echo "$ALL is out of date — add the missing imports"
  exit 1
fi

if [ "${1:-}" = "--per-file" ]; then
  pass=0
  fail=0
  while IFS= read -r name; do
    file="src/nova/$(echo "$name" | tr '.' '/').nova"
    if output="$("$APP" elab "$file" 2>&1)"; then
      pass=$((pass + 1))
    else
      fail=$((fail + 1))
      echo "FAIL: $name"
      echo "$output" | sed 's/^/  /'
    fi
  done < <(modules)
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

# ... and again under NOVA_GLOBAL_STORE=1, the migration escape hatch
# (the default is the SEARCHLESS discipline — SearchlessElaboration.md
# §5.3, docs/NovaElaboration.txt): the corpus must accept identically
# whether store use is scoped to the using-clauses or searched
if output="$(NOVA_GLOBAL_STORE=1 "$APP" elab "$ALL" 2>&1)"; then
  echo "$count/$count elaborations passed (global store)"
else
  echo "FAIL (global store): $ALL"
  echo "$output" | sed 's/^/  /'
  exit 1
fi
