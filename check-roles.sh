#!/usr/bin/env bash
# The mechanical half of the roles audit of docs/NovaStrategy.txt: the
# author–engine–kernel division, as far as it can be read off the
# tree (kernel closure, no escape hatches or backtracking in the
# kernel, the entry points, the one site that extends the kernel's
# signature, the engine's assumption sites). The judgement half is
# the checklist in the same document (the /roles-audit skill walks it).
set -e
cd "$(dirname "$0")"
python3 tools/check-roles.py
