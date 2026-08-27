# Defining your own types
%stub

Declaring a new type by listing the ways to build its values.

## The shape of a declaration

- A `data` item names a **sort** and its **constructors**.
- The simplest case: no parameters, no indices — a plain enumeration or
  a recursive type.
- Reading the notation: `U` marks the sort, `El q` marks a recursive
  position.

## Recursive types

- Lists, trees: constructors that take arguments of the type being
  defined.

## Parameters

- `[a : 𝕌]` prefixes abstract the whole declaration over a carrier, so
  `List a` is one definition, not one per element type.

## What you get back

- The sort, the constructors, and the **eliminators** — which is how
  you take a value apart ([Recursion](#recursion)).

## What is deferred

- Indices ([Indexed families](#indexed-families)) and equation
  constructors ([Quotient inductive-inductive types](#qiits)). This
  chapter stays in the fragment that matches a familiar `data`
  declaration.
