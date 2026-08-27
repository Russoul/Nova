# The `data` item: QIITs
%stub

One item introduces a quotient inductive-inductive signature, and
expands into ordinary definitions.

## The signature literal

```nova
data [a : 𝕌] [r : a → a → Ω] ( Q : U
     ; cls : a → El Q
     ; qeq : (x : a) (y : a) → r x y → cls x ≡ cls y ∈ El Q )
```

- `[x : T]` prefixes are **parameters**; every generated definition
  abstracts over them.
- Entries are sorts (`… → U`), point constructors (`… → El q`) and
  equation constructors (`… → l ≡ r ∈ El q`).

## Inductive versus external domains

- `El q` inside the literal marks an **inductive** domain: `q` must be
  a sort of the same literal, or an `≡` between elements of one.
- Any other surface type is **external**, and stands **bare** —
  `(n : ℕ)`, not `El ℕ`. The `El c` spelling of an external code still
  parses, but the canonical form is bare: `El` exists only in the ToS.
- A non-dependent domain may stand bare.
- A signature whose sorts are genuinely **large** has no code; an
  indexed large sort is a structural error, having no spelling in the
  closed-item discipline.

## What the item generates

- The sorts, the constructors, and **two** eliminators per sort:
  `<Sort>Elim` (code-valued motives, coherence hypotheses) and
  `<Sort>ElimP` (prop-valued motives, no coherences).
- Plus the equational lemmas the discharge engine needs (`.eq`,
  `.unfold`); [Generated names](#generated-names) is the naming table.

## Using an eliminator

- Argument order: motives, methods, coherence hypotheses, index spine,
  scrutinee.
- Use `ElimP` for equational goals — proof irrelevance closes the
  coherences.

## Equation constructors

- They impose a **judgemental** equality; no path terms exist, and `⋆`
  inhabits the reflected equation.
- Order-sensitive methods yield coherence obligations.

## Indexing and induction-induction

- Indexed sorts (`V : ℕ → U`), sorts indexed by other sorts, and
  recursive equation constructors.

## No generativity

- Signatures compare structurally: two textually identical `data`
  literals define the same type.
