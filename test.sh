#!/usr/bin/env bash
# Runs the golden test suite, then the elaboration gate.
#
# By default everything is built from source with pack. Setting
# NOVA_TESTS_BIN / NOVA_LSP_BIN / NOVA_BIN to already-built executables
# skips the corresponding build — that is how the Nix checks reuse the
# binaries `nix build` produced (see nix/checks.nix).
#
# The suite runs as NOVA_JOBS runner processes (default 8) over
# disjoint slices of the test list: a golden test is one process start
# of the binary under test, so the suite is bound by process starts,
# and the runner's own --threads gains nothing on this toolchain.
# With arguments (--only …, --timing, …) the suite runs in one process,
# as the runner would.
set -e

if [ -z "${NOVA_LSP_BIN:-}" ]; then
  pack build nova-lsp.ipkg
  export NOVA_LSP_BIN="$(pwd)/build/exec/nova-lsp"
fi

if [ -z "${NOVA_TESTS_BIN:-}" ]; then
  pack build nova-tests.ipkg
  NOVA_TESTS_BIN="$(pwd)/build/exec/nova-tests"
fi

jobs="${NOVA_JOBS:-8}"
if [ "$#" -gt 0 ] || [ "$jobs" -le 1 ]; then
  "$NOVA_TESTS_BIN" "$NOVA_TESTS_BIN" "$@"
else
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  find tests -name run | xargs -n1 dirname | xargs -n1 basename | LC_ALL=C sort > "$tmp/all"
  # the runner's --only matches a name as a SUBSTRING, so a name that
  # is part of another (elab-decl, elab-decl-…) must go with it, or two
  # runners run the same test at once and race on its scratch files
  python3 - "$tmp" "$jobs" <<'PY'
import sys
tmp, jobs = sys.argv[1], int(sys.argv[2])
names = open(f"{tmp}/all").read().split()
parent = list(range(len(names)))
def find(i):
    while parent[i] != i:
        parent[i] = parent[parent[i]]; i = parent[i]
    return i
for i, a in enumerate(names):
    for j, b in enumerate(names):
        if i < j and (a in b or b in a):
            parent[find(i)] = find(j)
groups = {}
for i, n in enumerate(names):
    groups.setdefault(find(i), []).append(n)
slices = [[] for _ in range(jobs)]
for g in sorted(groups.values(), key=len, reverse=True):
    min(slices, key=len).extend(g)
for k, sl in enumerate(slices):
    if sl:
        open(f"{tmp}/slice{k}", "w").write("\n".join(sl) + "\n")
PY
  for s in "$tmp"/slice*; do
    "$NOVA_TESTS_BIN" "$NOVA_TESTS_BIN" --only-file "$s" > "$s.log" 2>&1 &
  done
  wait
  cat "$tmp"/slice*.log | grep -v '^[0-9]*/[0-9]* tests successful$' | grep -v '^Failing tests:$' || true
  passed=$(cat "$tmp"/slice*.log | grep -E '^[0-9]+/[0-9]+ tests successful$' | awk -F/ '{s+=$1} END{print s+0}')
  failed=$(cat "$tmp"/slice*.log | grep -c ': FAILURE$' || true)
  echo "$passed/$((passed + failed)) tests successful ($jobs runners)"
  if [ "$failed" -ne 0 ]; then exit 1; fi
fi

./check-elaborations.sh
