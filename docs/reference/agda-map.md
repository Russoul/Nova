# Nova for Agda users
%stub

A map for readers arriving from Agda (or Idris, or Coq): what
translates directly, what is spelled differently, and what is simply
absent.

## The one-page table

- Side by side: `Set` / `𝕌`, `Prop`-ish / `Ω`, `data` / `data`,
  `refl` / `⋆`, `rewrite` / the discharge engine, holes, `where`.

## What translates unchanged

- Π and Σ, implicit arguments, operators as names, modules and imports,
  eliminators.

## Deep differences, in order of impact

1. **Equality reflects** — the subject of the next chapter, and the
   root of most of what follows.
2. **No coherence in types** — no `subst` in statements
   ([Types without coherence](#coherence)).
3. **No tactics, no `rewrite`** — an accepted equation becomes a
   candidate the engine applies, and each item names what it may use
   ([The discharge engine](#discharge)).
4. **Undecidable checking, by design** — what cannot be derived is
   *reported*, not rejected.
5. **One `data`, and it is a QIIT** — no separate quotient or
   higher-inductive mechanism ([QIITs](#qiits)).
6. **Two universes, no levels** — `𝕌` and `Ω`, no `Set₁`, no level
   polymorphism.
7. **No termination checker** — recursion is by eliminator only.
8. **A small trusted kernel** — the elaborator is untrusted and its
   output is re-checked.

## Habits to unlearn

- Reaching for `rewrite`; pattern-matching on `refl`; `with`-abstraction
  to expose an index; proving `subst` lemmas.

## Habits that transfer

- Stating general lemmas; naming what you use; induction with a motive.
