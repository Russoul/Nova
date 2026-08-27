# Quotients
%stub

Quotient types are primitive, and the relation is Ω-valued.

## The type

- `A / (x y. R)` with `R : Ω`; the name-dropping form `A / R`.
- Quotients by iff-equal relations are the **same** type, so a variable
  of one moves to the other with no coercion.

## Introduction and elimination

- `class t` builds a class.
- `quot-elim (z. T) (a. f) q` — motive, case function, scrutinee.

## Well-definedness

- `class a ≡ class b` is discharged automatically only when the relation
  is `∥𝟙∥`-shaped or an equation; otherwise supply the witness (`⋆ h`).
- Descending a **proposition** is free: at an Ω-valued motive, proof
  irrelevance closes the well-definedness goal outright
  (`el-prf-prop`). Descending data is what costs honest proofs.
- Where it is not free and the method is an explicit proof term, the
  goal is an equation **between proof terms**; name `prop.irrel` in
  `using`.

## Effectiveness

- When `class a ≡ class b` gives back `R a b` (`quotEffective.nova`,
  `intEffective.nova`).

## Worked example

- The integers as a quotient of `ℕ ⨯ ℕ`, and the rationals above them.
