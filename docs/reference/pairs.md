# Pairs and Σ-types
%stub

Dependent pairs, projections, and the code-versus-type trap.

## Σ-types

- `(x : A) ⨯ B` and the non-dependent `A ⨯ B`; binder groups iterate as
  for `→`.

## Pairing and projection

- `a , b` is right-associative, so nested pairs need no parentheses.
- `.π₁` and `.π₂` project and **infer**.

## η

- Σ-η is judgemental; `paireta` and `pairext` in `equality.nova` are the
  surface consequences.

## Codes versus types

- A Σ-**code** binds over a code, a Σ-**type** over a type. Getting this
  wrong drops the binder silently, and the error surfaces as
  `unknown name` at the use site, lines away.

## Records, idiomatically

- Structures as nested Σ-codes (`monoid.nova`, `group.nova`), and why
  laws are stated with `Id` rather than `≡` when they must live inside a
  code.
