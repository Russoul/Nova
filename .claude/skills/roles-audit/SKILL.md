---
name: roles-audit
description: The roles audit of docs/NovaStrategy.txt — check that the author–engine–kernel division still holds. Use after a phase of work on the kernel or the elaborator, whenever a module boundary or a Σ site changed, or when asked whether a change digresses from the division.
---

# Roles audit

Nova is three roles (docs/NovaStrategy.txt): the AUTHOR makes every
choice and writes statements; the ENGINE deterministically makes the
implicit explicit and emits derivations, never inventing a choice;
the KERNEL reads derivations with one reading per shape and is the
only trusted component. The audit checks that the tree still says so.

## 1. The mechanical half

```
./check-roles.sh
```

It must end with `the author–engine–kernel division holds`. A failure
names the check (K1–K4, S1, E1) and the site. Fix the tree, not the
check — unless the division itself was deliberately changed, in which
case docs/NovaStrategy.txt, tools/check-roles.py and the change go in
one commit.

## 2. The judgement half

Read the changes since the last audit (`git log` since the last commit
that touched docs/NovaStrategy.txt, or the range the user names) and
answer each question of the checklist in docs/NovaStrategy.txt, "The
audit", J1–J8, with a file:line for every "yes":

- J1 kernel reading depending on anything but shape and the given side
- J2 a second normalizer, or δ outside a named leaf, in the kernel
- J3 an engine rescue after a kernel rejection
- J4 an engine guess (type, motive, position, direction by trial or whitelist)
- J5 a NOVA_* flag on a verdict path
- J6 evidence persisting across runs
- J7 a certificate in surface clothing (path, budget, nth occurrence)
- J8 the reconstruction count: run the corpus audit and report the counts

```
NOVA_AUDIT=1 ./build/exec/nova elab src/nova/all.nova 2>&1 >/dev/null | grep -c 'REPLAY-FAIL\|PROOF-FAIL\|CHAIN-COMP'
```

## 3. The report

A short table: one row per question, verdict, and the site or "none".
A "yes" on J1–J7 is a digression: propose the revert, or record it in
docs/NovaStrategy.txt under "Where today digresses" with the plan that
closes it. J8 is the measure; report the number and whether it moved.
