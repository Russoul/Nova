# Holes and in-place elimination
%stub

A hole is a goal you write down. This chapter is the workflow built on
that: ask what belongs somewhere, have the checker case-split it for
you, and fill in the pieces.

## `?name`

- Checking-only, minted at the ambient context and the expected type,
  and reported with its full telescope.
- **Inert**: nothing solves it, nothing flips it into a definition,
  and a file containing one is never accepted.
- One `?x` per name per item; a repeat is a structural error.
- `(?x : T)` when the position does not determine the type.

## Reading a goal

- Everything left of `⊢` is what you have; right of it is what you
  owe.
- In an editor the same thing is a warning at the hole's own span, so
  hovering shows the goal without a re-run.

## Refinement

- A hole minted by the elaborator itself — an implicit with no source,
  a scrutinee's shape — is **synthetic**, and the run's own
  constraints usually say what it is. Reading them back turns
  scaffolding like `?p : ?p/imp3 ≡ ?p/imp4 ∈ ?p/imp0` into the goal
  you actually face, `?p : x ≡ y ∈ A`.
- Only synthetic holes are ever instantiated. A hole **you** wrote is
  your question, and answering it for you would be a guess.

## In-place elimination

- `nova eliminate <file> <line>:<col> <var>` fills the hole covering
  that position by eliminating the named variable of its context, and
  prints the resulting file.
- The line and column are the ones the report prints.
- What comes back is the eliminator with a fresh named hole per case:
  `λn. (ℕ-elim ?goalZ (n ih. ?goalS) n)`.
- Flags: `--deep` iterates a Σ split to the leaves, `--name` fills the
  next name slot, `--label` names the next new hole.

## What can be eliminated

- Which elimination a variable admits is read off its type.
- Hypotheses that depend on the variable are carried by the motive
  and re-applied — the closure rule, which subsumes the convoy
  pattern.

## The loop

- Write the statement, leave `?goal`, eliminate, fill each case,
  repeat. The worked example, end to end.
