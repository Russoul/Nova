# Definitions
%stub

Everything in a Nova file is a definition. This chapter is the shape of
one, and the two ways to write the thing on the right of it.

## `def`

- `def n : T ≔ t` — a name, its type, and its definition. That is the
  only item shape you need at first.
- Operators are names: `def + : ℕ → ℕ → ℕ ≔ …` defines the name `+`
  ([Operators and fixity](#operators)).

## Functions

- `λx. t` abstracts one argument at a time; application is
  juxtaposition, left-associative, as in any ML.
- The body of a `λ` extends **maximally** — as far right as it can. A
  `λ` that is a non-final pair component must be parenthesised.
- `A → B` is the non-dependent function type; the dependent form comes
  in [Π-types](#pi-types).

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

- `data` ([Quotient inductive-inductive types](#qiits)) and a `def` with clauses ([Defining equations](#clausal-defs)) are macros:
  they expand into ordinary items, and everything they provide reaches
  the file as plain `def`s.

## No local items

- Why parameters are Π-binders rather than a section mechanism, and what
  `let` ([`let`](#let)) does instead.
