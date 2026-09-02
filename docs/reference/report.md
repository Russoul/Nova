# Reading the report
%stub

What the checker prints, and what to do about each thing it prints.

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

## Open holes

- Reported with their telescopes, and covered in
  [Holes and in-place elimination](#holes).
- A bare `_` argument is a **blank**, not a hole: it is solved from
  the spine like an inserted implicit, and an unsolvable one is an
  error ([Implicit arguments and blanks](#implicits)).

## Recovery: one failure does not hide the rest

- An item that fails to elaborate is reported **at the item**, and the
  run continues with the next one — so a single broken proof no
  longer conceals every goal after it.
- The failed item's state is discarded; nothing it built reaches the
  signature. What replaces it is a **declaration** of its own
  signature, so later references still resolve, and that declaration
  blocks acceptance exactly as a written one does.
- Recovery never turns a failure into an acceptance.
- Items with nothing to declare — a `data` literal, or a `def` whose
  *type* failed — are skipped, and an unresolvable import is not
  recoverable at all.

## Declarations

- A `def` with a type and no definiens is a **named** placeholder: the
  name is usable below, and the file is not accepted until it is
  filled in.
- Reported under `open declarations` as `[name] ⊢ ? : T` — the
  top-down workflow, and the abstract-interface idiom (declare a
  carrier and its laws, program against them).

## Errors

- Parse errors, unknown names, mode errors — where they are reported and
  why the location can be one binder late.
