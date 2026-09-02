# Σ-types: dependent pairs
%stub

Pairs whose second component's type depends on the first.

## Syntax

- `(x : A) × B` and the non-dependent `A × B`; binder groups iterate as
  for `→`.
- `a , b` is right-associative, so nested pairs need no parentheses.
- `.π₁` and `.π₂` project.

## What the dependency is for

- "A number, together with a vector of that length."
- "A value, together with a proof about it" — the subset idiom.

## η

- Σ-η is judgemental: a pair is its two projections
  (`paireta`, `pairext` in `equality.nova`).

## Structures and records

- Nova has no record syntax; a structure is a nested Σ-code
  (`IsMonoid`, `IsGroup`).
- Why the laws inside such a code are stated with `Id` rather than `≡`
  ([Universes](#universes) explains what may live inside a code).

## Codes versus types

- A Σ-**code** binds over a code, a Σ-**type** over a type. The error
  for getting it wrong shows up at the use site, not the binder.
