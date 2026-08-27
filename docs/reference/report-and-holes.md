# Reading the report, and asking with holes
%stub

What the checker prints, what to do about each thing it prints, and how
to ask it questions.

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

## Asking questions

- There is **no `?goal` syntax**: term-level holes were removed
  deliberately (they were the dominant elaboration cost and the only
  source of non-monotone signature mutation). What replaces them:
- `⋆` marks an owed proof, and hovering it in an editor shows its
  goal; an obligation prints the same goal with its context.
- A bare `_` argument is a **blank**, solved from the spine like an
  inserted implicit — not a hole, and an unsolvable one is an error
  ([Implicit arguments and blanks](#implicits)).

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
