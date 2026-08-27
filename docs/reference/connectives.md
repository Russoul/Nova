# And, or, not: the logical connectives
%stub

Ordinary logic, built rather than built in.

## Squashing

- `∥T∥` turns any type into a proposition by forgetting *which*
  inhabitant you had.
- Why that forgetting is what makes a proposition a proposition.

## The connectives are definitions

- `⊤ ≔ ∥𝟙∥`, `⊥ ≔ ∥𝟘∥`, `p ∧ q`, `p ⊃ q`, `¬ p`, `p ∨ q` — all in
  `prop.nova`, none of them primitive.
- `∨` is impredicative: it quantifies over all of `Ω`.

## Using them

- Introduction with `⋆ e`; elimination with `squash-elim`.
- Elimination goes only into further propositions, and what to do when
  you need data out of a proof.

## Implication versus the function arrow

- `p ⊃ q` and `p → q` both exist; when each is the right one.
