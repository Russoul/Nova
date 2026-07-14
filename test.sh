#!/usr/bin/env bash
set -e
pack run nova-foundation-tests.ipkg "$(pwd)/build/exec/nova-foundation-tests" "$@"
./check-derivations.sh
