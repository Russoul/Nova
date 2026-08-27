# Items: the shape of a file
%stub

A file is a sequence of items. Every item is declared in the empty
context.

## `def` — definitions

- `def n : T ≔ t`.
- Operators are names: `def + : ℕ → ℕ → ℕ ≔ …` defines the name `+`.

## `type` — type definitions

- `type X ≔ T`, the `A = 𝕍` instance of the one definition entry form.

## Declarations

- `def n : T` with no definiens declares `n` abstractly — a named rigid
  hole. References are stuck, but a declared **equation** registers as a
  lemma: the abstract-interface idiom (declare a carrier and its laws,
  program against them).
- A file with a declaration is never accepted until the definiens lands.

## The `using` clause

- `using (a, b)` fixes the item's **discharge scope**. [`using`: licences and scope](#using-clauses)
  is about choosing it.

## Item macros

- `data` ([The `data` item](#data)) and a `def` with clauses ([Defining equations](#clausal-defs)) are macros:
  they expand into ordinary items, and everything they provide reaches
  the file as plain `def`s.

## No local items

- Why parameters are Π-binders rather than a section mechanism, and what
  `let` ([`let`](#let)) does instead.
