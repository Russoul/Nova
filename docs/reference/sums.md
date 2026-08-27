# Sums
%stub

The disjoint union `⊎`, with Agda's notation.

## The type

- `A ⊎ B` is **non-dependent** and right-associative, and binds tighter
  than `→ ⨯ /` — so `A ⊎ B → C` is `(A ⊎ B) → C`.

## Introduction and elimination

- `inj₁ t`, `inj₂ t` (checking-only).
- `⊎-elim (w. T) (a. l) (b. r) t` — motive, left case, right case,
  scrutinee.

## Computation

- β on each injection is judgemental; the η law is stated judgementally
  in the theory and reproved on the surface by case analysis at an
  equality motive.

## Derived facts

- Injectivity and disjointness need no rules: a retraction plus
  congruence gives injectivity, and transporting an `is-left` code gives
  disjointness. Both are in `sum.nova`.
