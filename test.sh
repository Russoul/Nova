#!/usr/bin/env bash
set -e
pack run nova-tests.ipkg "$(pwd)/build/exec/nova-tests" "$@"
./check-elaborations.sh
