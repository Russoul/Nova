# Pitfalls
%stub

The failures that cost the most time, with their symptoms.

## Parenthesising

- Equality-typed motives and λ bodies need parentheses.
- A λ that is a non-final pair component must be parenthesised.

## Codes versus types

- A Σ-code binds over a code, a Σ-type over a type; writing the wrong
  one silently drops the binder and the error surfaces at the use.

## Licences

- More `.eq` can undo a proof; hints list what a route *could* use, not
  what this proof needs.

## Chains

- A chain runs with an empty Σ-scope; a link needing a licensed
  conversion fails. Rewrite it as `trans`.
- A link rewriting inside a `quot-elim` scrutinee fails at replay.

## Quotients

- `class a ≡ class b` auto-discharges only for `∥𝟙∥`-shaped or
  equational relations; otherwise supply the witness.
- `class X ≐ class Y` does **not** follow from `X ≐ Y` by a lemma — name
  the congruence.

## Transport

- `transport`'s family lands in `𝕌`; for one landing in `Ω` use
  `transportP`. The wrong choice is reported as
  `λ checked against a non-Π type`.

## Kernel approximations

- `ℕ-elim` proofs used as rewrite-step arguments are constant-motive
  only; state the dependent fact as a named lemma instead.

## Lexical traps

- Greek letters are not identifiers; `--` inside an operator is a
  comment.
