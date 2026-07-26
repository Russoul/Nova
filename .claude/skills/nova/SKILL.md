---
name: nova
description: Programming and proving in Nova (.nova surface files) — the elab/obligation loop, surface syntax, lemma-based discharge, QIITs. Use when writing or fixing .nova files, proving equations, or debugging why a file is not accepted.
---

# Programming and proving in Nova

Nova is an Extensional Computational Type Theory: equality reflection,
no tactics, no rewrite-rule declarations. You prove things by writing
ordinary definitions whose ≡-typed statements the DISCHARGE ENGINE then
uses automatically. The trusted kernel replays certificates; you never
interact with it directly.

## The loop

```
pack build nova.ipkg              # once per source change
build/exec/nova elab file.nova    # check one file
./test.sh                         # full suite (golden tests + corpus)
```

A file is ACCEPTED iff the run ends with `Accepted.` (zero obligations).
Otherwise you get a report:

```
open obligations (1):
  [1] (x : El ℕ) (m : El (Bag ℕ)) ⊢ lhs ≐ rhs : T
      at: def foo: checking Refl
```

Each obligation is an equation, under binders, that the engine had to
ASSUME. Your job: make it derivable, then re-run.

## How discharge works (the key mental model)

Every accepted `def` whose type is an equation (possibly under Π-binders)
enters the lemma store E and becomes a discharge candidate for
EVERYTHING BELOW it. The engine applies candidates in three ways:

- REWRITING: oriented, size-decreasing/non-permutative instances are
  used as left-to-right rules at any subterm, to a fixpoint.
- WHOLE-EQUATION MATCH: the goal (or its flip) matches a candidate's
  sides under one consistent first-order instantiation; unbound
  parameters must carry ≡ (or 𝟙 / Prf) types whose instances discharge
  as side conditions. This is how PERMUTATIVE lemmas (commutativity,
  exchange) and hypothesis-conditional lemmas fire — they never rewrite
  (they would oscillate).
- TRANSITIVITY HOPS: a candidate may rewrite one side wholesale, with a
  small depth budget.

Matching is first-order and up to El-decoding (`El ℕc ≜ ℕ`), so a
GENERIC lemma discharges its instantiated goals: prove `swapG : (a : 𝕌)
… ∈ El (Bag a)` once and every `Bag ℕ` instance follows.

Consequences:
- ORDER MATTERS. A lemma helps only items after it. Discharge an
  obligation by adding a def ABOVE the failing item.
- Candidates are stored normalized as of their acceptance point.
- An obligation assumed once is not re-reported, but it is NOT proven —
  check the final count, not the noise.

## Proving recipe

1. Read obligation [1]. State it verbatim as a def: binders become
   Π-arguments, the equation becomes the ≡-type.
2. Try `≔ λx. … Refl` first — β + already-stored lemmas may close it.
3. Otherwise prove by induction with an eliminator and an ≡-typed
   motive (PARENTHESIZE the motive: `(k. Z + k ≡ k ∈ ℕ)` — equality
   types don't parse bare in binder-body positions):

   ```
   def zeroPlusId : (n : ℕ) → Z + n ≡ n ∈ ℕ ≔
     λn. ℕ-elim (k. Z + k ≡ k ∈ ℕ) Refl (k ih. Refl) n
   ```

   In the step case, `ih` is in scope and in E — `Refl` usually closes.
4. Re-run. Repeat for the next obligation. Prefer general lemmas over
   instance-specific ones (they discharge whole families of goals).

## Surface syntax (grounded in src/nova/)

Items (always top-level, closed):
```
def x : T ≔ t                     -- definition
type X ≔ T                        -- type definition
import M                          -- M.x qualified;  import M (a, b) opens a, b
infixl 6 +                        -- fixity; operators ARE names: def + : ℕ → ℕ → ℕ ≔ …
data [a : 𝕌] ( … )                -- QIIT signature (see below)
```

Types: `𝟘 𝟙 ℕ 𝕌 Ω`, `(x : T) → U` and `T → U`, `(x : T) ⨯ U`,
`l ≡ r ∈ T`, `El t`, `T / (x y. r)` (r is Ω-valued), `Prf p`.
`∥T∥` squashes any type to a proposition (an Ω-element).

Elements: `λx. t`; application by juxtaposition; `(t : T)` ascription
(the lever into inference mode); `(a , b)` pairs with `.π₁`/`.π₂`
projections; `Z`, `S t`; `Refl`;
`ℕ-elim (n. T) z (n ih. s) t` (motive first);
`class t` (quotient intro); `quot-elim (x. T) (a. f) q`;
`⋆` (canonical proof; `⋆ e` with explicit witness);
`squash-elim e (x. body)`. Universe codes are written like their types
(`𝟘 𝟙 ℕ`, `(x : t) → u`, `l ≡ r ∈ t`).

Comments: `--`. Proof irrelevance is judgemental (`Prf`), and
propositional extensionality holds at Ω.

## QIITs (the data item)

```
data [a : 𝕌] [r : El a → El a → Ω]
     ( Q   : U
     ; cls : (x : El a) → El Q
     ; qeq : (x : El a) (y : El a) (h : Prf (r x y)) → cls x ≡ cls y ∈ El Q )
```

- `[x : T]` prefixes are PARAMETERS; every generated def abstracts over
  them (`cls a r x`, `Q a r`).
- Entries: `Name : binders → U` (sort), `… → El q` (point constructor),
  `… → l ≡ r ∈ El q` (equation constructor — imposes a JUDGEMENTAL
  equality; no path terms exist, `Refl` inhabits the reflected ≡).
- Binder domains: `(x : El q)` with q a sort/code is INDUCTIVE;
  anything else is EXTERNAL. Write external naturals as `El ℕ`, not
  `ℕ` — a non-code external domain makes the signature LARGE and a
  large sort cannot be code-valued or parameterized.
- Generated names: the sorts, the constructors, one eliminator per
  sort named `<Sort>Elim`.
- Eliminator argument order: motives (one per sort, `λw. T` with w the
  self argument), then methods (one per point constructor: value and IH
  binders interleaved, e.g. `λx. λr. λih. …`), then one COHERENCE
  HYPOTHESIS per equation constructor (an ≡-typed argument; pass
  `λ…. Refl` when the method is order-insensitive), then index spine,
  then the scrutinee. Example:

  ```
  def size : (a : 𝕌) → El (Bag a) → ℕ ≔
    λa. λm. BagElim a (λb. ℕ) Z (λx. λr. λih. S ih) (λx. λy. λr. λih. Refl) m
  ```

- β holds on the nose; closed computations discharge by `Refl`.
- No generativity: signatures compare structurally — two textually
  identical `data` literals define THE SAME type.
- Induction-induction (sorts indexed by other sorts) and recursive
  equation constructors are supported; for IH-bearing coherences, prove
  the twin equation as a standalone lemma first and pass `Refl`.

## Pitfalls

- Equality-typed motives and λ-bodies need parentheses.
- A method that is order-sensitive w.r.t. an equation constructor
  yields a coherence obligation — discharge it with a lemma like any
  other (or make the method insensitive).
- ℕ-elim proofs used as rewrite-step arguments are constant-motive
  only (kernel approximation A1); if a dependent-motive fact is needed
  as a step, state it as a named lemma and let whole-equation match
  apply it.
- Permutative facts (commutativity, exchange) never auto-rewrite; they
  only fire via whole-equation match — state the exact shape you need
  (e.g. `a + (b + c) ≡ b + (a + c)`).
- The obligation report shows NORMALIZED sides; state lemmas against
  what the report prints, not against your source spelling.

## Where to look things up

- `docs/NovaFoundation.txt` — the theory, sole source of truth; every
  rule is named and those names are cited in code comments.
- `docs/NovaElaboration.txt` — surface syntax and the discharge engine.
- `docs/NovaKernel.txt` — certificates and approximations (A1–A6).
- `docs/NovaPipeline.txt` — the trust architecture.
- `src/nova/` — the corpus, one topic per file: `nat` (arithmetic),
  `equality`/`prop` (≡ and Ω), `quotient`/`quottyuniv` (quotients),
  `vect`/`vectAppend` (𝕌-indexed families), `qiitNat`/`qiitBag`/
  `qiitQuot`/`qiitVec` (QIIT basics), `qiitInt` (recursive equations),
  `qiitConTy` (induction-induction), `qiitCross` (definitions built on
  earlier QIITs), `integer*` (a worked development).
- `python3 tools/render-specs.py` renders the specs to navigable HTML
  (`build/docs/specs.html`); `--check` cross-checks rule names against
  the sources.
