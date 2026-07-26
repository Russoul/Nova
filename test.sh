#!/usr/bin/env bash
set -e
pack build nova-lsp.ipkg
export NOVA_LSP_BIN="$(pwd)/build/exec/nova-lsp"
pack run nova-tests.ipkg "$(pwd)/build/exec/nova-tests" "$@"
./check-elaborations.sh
pack run nova-compute-tests.ipkg
