# Checking, inference and ascription
%stub

Elaboration is bidirectional. Knowing which mode you are in explains
most "why does it not typecheck" moments.

## The two modes

- **Checking**: the expected type is known; introduction forms
  (`λ`, pairs, `inj₁`/`inj₂`, `corec`, `⋆`, calc chains) are
  checking-only.
- **Inference**: the type is computed from the term; variables,
  applications, projections, `out`, ascriptions infer.

## Ascription

- `(t : T)` is the lever into inference mode.
- Where it is required: a λ or pair applied or projected directly, an
  eliminated term whose type the elaborator cannot see.

## Motives and carriers

- `ℕ-elim`, `⊎-elim` and `quot-elim` take their motive **inline** when
  they must infer: a motive is not recoverable without higher-order
  unification.
- The motive group is optional, and dropping it makes the eliminator
  **checking-only** — the motive comes from the expected type. That is
  the spelling the corpus uses almost everywhere
  (`ℕ-elim ⋆ (k ih. ⋆) n`).
- `corec` always takes its state carrier inline: it cannot be read off
  the expected `ν`-type.

## Diagnosing a mode error

- `λ checked against a non-Π type` and friends: what they mean.
