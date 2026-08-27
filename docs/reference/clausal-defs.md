# Defining equations
%stub

A `def` with clauses is an item macro that gives you pattern-matching
syntax plus the lemmas that make it usable.

## Syntax

```nova
def plus : ℕ → ℕ → ℕ
  | plus Z n ≔ n
  | plus (S m) n ≔ S (plus m n)
```

- Every clause opens with `|`; the head is the item's own name; infix
  spelling works when a fixity is in scope.
- Patterns are constructor spellings and variables, to any depth; the
  supported fragment demands depth 1.

## What it expands into

- The definition proper (a synthesized eliminator), one Π-closed
  **equation lemma** per clause, and the pointwise **uniqueness**
  lemma — the three pieces of the contractibility contract.

## Naming the generated lemmas

- `[name]` after the type names the uniqueness lemma; `[name]` after a
  clause names that clause's equation lemma. An operator-named item has
  no identifier to prefix, so every generated name is overridden.

## The witness form

- Supplying `≔ t` alongside clauses: existence by hand, clause lemmas
  paid with `⋆`, uniqueness still synthesized.

## What is in the fragment

- Structural recursion, recursion at a changed trailing argument, `⊎`
  splits, the no-split single clause, nested recursive calls.
