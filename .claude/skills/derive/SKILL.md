---
name: derive
description: Synthesize or check a Nova Foundation derivation (contexts/types/elements judgements, .rules/.target files) using the nova-foundation-app session checker. Use whenever asked to prove, derive, or check a judgement like ctx-wf/ty-wf/el-wf/el-eq, or to work with files under derivations/ or tests/foundation/derivation/.
---

# Deriving in Nova Foundation

`nova-foundation-app` is a checker for the Nova Foundation type theory (contexts,
types, elements, substitutions, telescopes, spines). It can check a whole
proof in one shot (`check`), or build one incrementally, one rule at a time,
with immediate accept/reject feedback (`init`/`apply`/`query`/`dump`/`undo`).
Prefer the incremental workflow when synthesizing a derivation from scratch —
it gives you a tight feedback loop instead of writing a whole `.rules` file
blind and finding out at the end which line broke.

## Read the spec, not the implementation

- **Syntax and grammar**: `src/text/Internals/NovaSyntax.txt` — the concrete
  grammar for contexts/types/elements/rules, keyword-first typing-rule and
  judgement-form syntax.
- **Rule semantics**: `src/text/Internals/NovaFoundation.txt` — what each
  judgement means and the natural-deduction rules behind each keyword.
- **Rule cheat sheet**: `docs/derivation-rules-cheatsheet.md` — one line per
  typing rule keyword: premises → conclusion. Use this to pick which keyword
  proves a given judgement shape, instead of reading `Derivation.idr`.
- **`src/idris/Nova/Foundation/*.idr` is implementation, not spec.** Only
  read it when a `Rejected` reason looks like a checker bug (e.g. a rule
  that should apply doesn't) rather than a wrong proof step on your part.

## Build once, then call the binary directly — never `pack run` in the loop

```sh
pack build nova-foundation.ipkg
```

After that, always invoke the compiled wrapper script directly:

```sh
build/exec/nova-foundation-app <command> ...
```

`pack run nova-foundation.ipkg ...` re-resolves the package/build graph on
every call — about **2.9s per invocation** — versus **~50ms** for the
already-built binary. In an incremental loop of dozens of `apply`/`query`
calls that difference is the entire point of this workflow; only use `pack
build`/`pack run` again after editing the Idris sources themselves.

## Commands

A **session** is just the text of a `.rules` file: a sequence of
`- <TypingRule>` lines, always empty or newline-terminated. Applying a rule
either appends it (canonically pretty-printed) or leaves the file untouched.

```sh
# Start a fresh, empty session file.
build/exec/nova-foundation-app init derivations/<goal>/session.rules

# Try one candidate rule. On success: appends it and prints the newly
# derived facts. On failure: prints the rejected rule + precise reason,
# and leaves the session file untouched (safe to retry other candidates).
build/exec/nova-foundation-app apply derivations/<goal>/session.rules "ctx-emp"
build/exec/nova-foundation-app apply derivations/<goal>/session.rules "ty-nat ε ⊦ ℕ"

# Check whether a target judgement is derivable so far, without mutating
# the session. Cheap — use it as read-only lookahead before committing to
# a chain of `apply`s toward a hypothesis.
build/exec/nova-foundation-app query derivations/<goal>/session.rules "ty-wf ε ⊦ ℕ"

# List everything derived so far. Filter by judgement kind (ctx-wf, ctx-eq,
# sub-wf, sub-eq, ty-wf, ty-eq, el-wf, el-eq, tel-wf, tel-eq, sp-wf, sp-eq)
# once the session has any size — an unfiltered dump costs context.
build/exec/nova-foundation-app dump derivations/<goal>/session.rules
build/exec/nova-foundation-app dump derivations/<goal>/session.rules el-wf

# Drop the last accepted rule (backtrack one step).
build/exec/nova-foundation-app undo derivations/<goal>/session.rules

# One-shot batch check of a complete rules file against target judgements
# (both files use "- <rule>" / "- <judgement>" lines). Useful for a final
# check, or for re-verifying a session file someone else finished.
build/exec/nova-foundation-app check derivations/<goal>/session.rules derivations/<goal>/session.target
```

## Recommended loop

1. `init` a session file for the goal.
2. Repeatedly `apply` candidate rules. A rejection is free information, not
   a wasted step — it never corrupts the session, so try things liberally
   rather than trying to reason out the whole proof before touching the
   tool.
3. Use `query` to sanity-check a hypothesis ("is this sub-goal derivable
   yet?") before spending several `apply` calls building toward it.
4. Use `dump <kind>` when you lose track of what's already been proven,
   e.g. after a context reset, instead of re-deriving it from memory.
5. Use `undo` to back out of a dead end rather than starting a new session.
6. Once the target is derivable (`query` says `Derivable`), write its
   `.target` file and run `check` once end-to-end as a final sanity check.

## Session file convention (cross-session / cross-agent handoff)

Keep each goal's session under `derivations/<goal-name>/`:

```
derivations/<goal-name>/session.rules   # the growing proof script
derivations/<goal-name>/session.target  # the judgement(s) being proven
```

Because a session is nothing but a plain-text file, this convention is
enough for cross-session and cross-agent handoff: any agent (or a human)
picks up someone else's in-progress proof by reading that path — no shared
memory or live process needed. `dump` immediately reconstructs "what's
already been proven" without replaying the conversation history. Different
agents can own different `derivations/<goal-name>/` directories in
parallel; ordinary git (branches, commits) is enough to coordinate.

A finished, checked derivation can also be promoted into a reusable lemma:
add its result to the signature with a `sig` rule (`sig Γ ⊦ x ≔ t : T`) and
later sessions can reference it by name (`sig-var x` / `sig-var-eq x`)
instead of re-deriving it.
