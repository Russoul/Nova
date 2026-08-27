# What dependent types are
%stub

The central idea, in one chapter, before any of the machinery.

## Types that mention values

- In most languages, types and values live in separate worlds. Here a
  type may **mention** a value: `Vect n a` is a type built from the
  number `n`.
- Consequently a function's result type can depend on its argument.

## The two shapes

- **Π** — a function type whose codomain mentions the argument:
  `(n : ℕ) → Vect n a`.
- **Σ** — a pair type whose second component's type mentions the first:
  `(n : ℕ) ⨯ Vect n a`.
- Familiar arrows and products are the special case where the
  dependency is unused.

## What this buys

- Specifications that pin down behaviour, not just shape.
- Statements: `(n m : ℕ) → n + m ≡ m + n` is a type, and a value of it
  is a proof.

## What it costs

- The checker must now decide when two *types* are equal, because
  `Vect (n + 0) a` and `Vect n a` are written differently. How Nova
  answers that is [Reflection](#reflection), and it is the design
  decision the rest of the book turns on.

## Where to go next

- The mechanics: [Π-types](#pi-types), [Σ-types](#sigma-types),
  [Universes](#universes).
