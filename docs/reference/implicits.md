# Implicit arguments and blanks
%stub

Brace binders, how they are recovered, and how to override them.

## Brace binders

- `{x : A} → B` marks an implicit Π-binder; `{a b : 𝕌}` groups as
  everywhere.
- Implicitness is per-definition metadata, never core syntax.

## Insertion

- Inserted at application spines; in checking position, trailing
  implicits insert too.
- `f {}` is the no-insert marker for passing the bare function.

## Recovery

- Rigid first-order matching against the expected type: what is
  recoverable, and what is not.

## Explicit override

- `f {t}` passes an implicit positionally.

## Blanks

- A bare `_` in an argument position of an applied ordinary definition
  is a **blank**: a per-site elided *explicit* argument, solved by the
  same oracle that solves an inserted implicit.
- A blank never binds to an implicit position, never appears in
  constructor or eliminator spines, and an unsolvable blank is a
  structural error naming the remedy.
