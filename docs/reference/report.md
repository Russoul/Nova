# Reading the report
%stub

What the elaborator prints, and what to do about each thing it prints.

## Acceptance

- Zero obligations, zero holes.

## Obligations

```text
open obligations (1):
  [1] (x : ℕ) (m : Bag ℕ) ⊢ lhs ≐ rhs : T
      at: def foo: checking ⋆
```

- An obligation is an equation, under binders, that the engine had to
  **assume**. It is not an error and not a proof.
- Sides are printed **normalised**: state lemmas against what the report
  prints, not against your source spelling.
- An obligation assumed once is not re-reported — check the final count,
  not the noise.
- The `hint:` line usually names the licence a route could use.

## Holes

- `?name` is a rigid hole: the run continues and the report prints its
  context and type. A file with `?` holes is never accepted.
- `_name` / `_` are solvable: the elaborator may instantiate them when
  an equation pins them, and a fully solved file **is** accepted with
  the `_`s left in the source.

## Declarations

- A `def` without a definiens is reported under open holes; acceptance
  stays blocked until it is supplied.

## Errors

- Parse errors, unknown names, mode errors — where they are reported and
  why the location can be one binder late.
