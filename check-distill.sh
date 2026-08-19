#!/usr/bin/env bash
# The corpus round-trip gate of docs/NovaPerfectSurface.txt (Phase 1):
# distill the whole corpus and verify — re-parsed ASTs structurally
# identical, re-elaboration identical, both runs accepted.
set -e
pack build nova.ipkg
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
build/exec/nova distill src/nova/all.nova "$tmp"
