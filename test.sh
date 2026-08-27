#!/usr/bin/env bash
# Runs the golden test suite, then the elaboration gate.
#
# By default everything is built from source with pack. Setting
# NOVA_TESTS_BIN / NOVA_LSP_BIN / NOVA_BIN to already-built executables
# skips the corresponding build — that is how the Nix checks reuse the
# binaries `nix build` produced (see nix/checks.nix).
set -e

if [ -z "${NOVA_LSP_BIN:-}" ]; then
  pack build nova-lsp.ipkg
  export NOVA_LSP_BIN="$(pwd)/build/exec/nova-lsp"
fi

if [ -n "${NOVA_TESTS_BIN:-}" ]; then
  "$NOVA_TESTS_BIN" "$NOVA_TESTS_BIN" "$@"
else
  pack run nova-tests.ipkg "$(pwd)/build/exec/nova-tests" "$@"
fi

./check-elaborations.sh
