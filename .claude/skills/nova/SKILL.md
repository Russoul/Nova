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
      at: def foo: checking ⋆
```

Each obligation is an equation, under binders, that the engine had to
ASSUME. Your job: make it derivable, then re-run.

HOLES: write `?name` (rigid) for any element (checking position only —
ascribe if you must use one where a type would be inferred) or any
type. The run continues and the report lists each hole with its
context and type (`open holes (n): [?name] (x : ℕ) ⊢ ? : T — at: def
foo`) — use them to ask the elaborator "what goes here?". A file with
`?`-holes is never accepted. SOLVABLE holes `_name`/`_` may instead be
INSTANTIATED by the elaborator when an equation pins them directly
(`S _m ≡ S (S Z) ∈ ℕ` solves `_m ≔ S Z`); solved holes unfold like
definitions and a fully-solved file IS accepted with the `_`s left in
the source. A hole nothing pins stays open and is reported. Reusing a
hole name refers to the same hole (same context or under more
binders); `_`-leading identifiers are reserved.

DECLARATIONS: `def x : T` with no `≔` declares x abstractly — a named
rigid hole in Σ. References are stuck; a declared EQUATION registers
as a lemma (the abstract-interface idiom: declare a carrier and its
laws, program against them). Reported under open holes; acceptance
stays blocked until the definiens is supplied.

## How discharge works (the key mental model)

Every accepted `def` whose type is an equation (possibly under Π-binders)
enters the lemma store E and becomes a discharge candidate for
EVERYTHING BELOW it. The engine applies candidates in three ways:

- WHOLE-EQUATION MATCH: the goal (or its flip) matches a candidate's
  sides under one consistent first-order instantiation; unbound
  parameters must carry ≡ (or 𝟙 / Prf) types whose instances discharge
  as side conditions. This is how PERMUTATIVE lemmas (commutativity,
  exchange) and hypothesis-conditional lemmas fire. **A parameter that
  occurs in NEITHER side can never be bound** — a candidate carries no
  type slot, so a lemma whose parameter appears only in the equation's
  type is unusable and its goal comes back verbatim, unhinted (B-21).
- CONGRUENCE DESCENT: one deterministic descent through the two sides'
  common structure, each child discharged by the above. Together with
  whole-equation match this covers most goals, which is why the
  group/ring modules cite no rewrite at all.
- REWRITING, only if licensed: oriented, size-decreasing/non-permutative
  candidates are used as left-to-right rules at any subterm — but ONLY
  when the site cites `hyp.rw` or `<lemma>.rw`. A plain citation does
  NOT make a lemma a rewrite rule (B-22). Reach for `.rw` when the redex
  sits under a different head, where congruence cannot descend.
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
2. Try `≔ λx. … ⋆` first — β + already-stored lemmas may close it
   (⋆ is the proof of EVERY proposition, equations included; there is
   no Refl).
3. Otherwise prove by induction with an eliminator and an ≡-typed
   motive (PARENTHESIZE the motive: `(k. Z + k ≡ k ∈ ℕ)` — equality
   types don't parse bare in binder-body positions):

   ```
   def zeroPlusId : (n : ℕ) → Z + n ≡ n ∈ ℕ ≔
     λn. ℕ-elim (k. Z + k ≡ k ∈ ℕ) ⋆ (k ih. ⋆) n
   ```

   In the step case, `ih` is in scope and in E — `⋆` usually closes.
   Over a QIIT, use the PROP eliminator `<Sort>ElimP` for equational
   goals (Ω-valued motives, NO coherence arguments):

   ```
   def plusQzr : (a : El N) → plusQ a z ≡ a ∈ El N ≔
     λa. NElimP (λn. (plusQ n z ≡ n ∈ El N)) ⋆ (λn. λih. ⋆) a
   ```
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
`T ⊎ U` (non-dependent disjoint union; binds TIGHTER than → ⨯, so
`A ⊎ B → C` is `(A ⊎ B) → C`),
`l ≡ r ∈ T` (SUGAR for `Prf (l ≡ r ∈ T)` — equality is an Ω-valued
PROPOSITION), `El t`, `T / (x y. r)` (r is Ω-valued), `Prf p`,
`ν F` (coinductive type at a one-hole polynomial `F ::= 𝕏 | K t |
F ⨯ F | F ⊎ F | (x:t) ⨯ F | (x:t) → F` — external pieces are codes;
e.g. `ν (K a ⨯ 𝕏)` is streams of `a`).
`∥T∥` squashes any type to a proposition; `∥Prf p∥ ≜ p`.

Elements: `λx. t`; application by juxtaposition; `(t : T)` ascription
(the lever into inference mode); `(a , b)` pairs with `.π₁`/`.π₂`
projections; `Z`, `S t`; `l ≡ r ∈ T` (the equality prop, at Ω —
the ∈-slot takes a TYPE, so write `∈ El a` for a code `a`);
`ℕ-elim (n. T) z (n ih. s) t` (motive first);
`inj₁ t`/`inj₂ t` (sum intros, checking-only) and
`⊎-elim (w. T) (a. l) (b. r) t` (motive, left case, right case,
scrutinee — β on both injections);
`class t` (quotient intro); `quot-elim (x. T) (a. f) q`;
`out t` (the coinductive observation — infers, like the projections)
and `corec (x : a. f) u` (corecursor: carrier code `a`, coalgebra
body `f` over `x : El a`, seed `u` — checking-only, the polynomial
comes from the expected ν-type; β: `out (corec …)` runs one step);
`coind (x y. R) p (x y h. q)` (COINDUCTION, el-nu-coind, checked at
`Prf (l ≡ r ∈ El (ν F))`: invariant `R` at Ω over the two sides,
`p : Prf (R l r)`, and `q` the one-step closure — under generic
`x y` and `h : Prf (R x y)`, prove the observations RELATOR-related.
Idioms: conjunction/existential invariants are squashed Σs —
`squash-elim h (w. ⋆ (…))` unpacks them, and the engine harvests
`w`'s projected equations automatically; `u ≡ ⟨machine⟩`-shaped
components act as unfold-once rewrite rules. See stream.nova's
tlCons and streamBisim.nova's bisimReflect);
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
  equality; no path terms exist, `⋆` inhabits the reflected Prf).
- Binder domains: `(x : El q)` with q a sort/code is INDUCTIVE;
  anything else is EXTERNAL. Write external naturals as `El ℕ`, not
  `ℕ` — a non-code external domain makes the signature LARGE and a
  large sort cannot be code-valued or parameterized.
- A NON-DEPENDENT domain may stand bare: `cls : El a → El Q` is
  `(x : El a) → El Q` with an anonymous binder; bare and named
  binders mix freely (`vcons : (n : El ℕ) → El (V n) → El (V (S n))`).
- Generated names: the sorts, the constructors, and TWO eliminators
  per sort: `<Sort>Elim` (code-valued motives `… → 𝕌`, coherence
  hypotheses) and `<Sort>ElimP` (prop-valued motives `… → Ω`, results
  through Prf, NO coherence arguments — proof irrelevance closes
  them). Use ElimP for equational goals.
- Eliminator argument order: motives (one per sort, `λw. T` with w the
  self argument), then methods (one per point constructor: value and IH
  binders interleaved, e.g. `λx. λr. λih. …`), then one COHERENCE
  HYPOTHESIS per equation constructor (an ≡-typed argument; pass
  `λ…. ⋆` when the method is order-insensitive), then index spine,
  then the scrutinee. Example:

  ```
  def size : (a : 𝕌) → El (Bag a) → ℕ ≔
    λa. λm. BagElim a (λb. ℕ) Z (λx. λr. λih. S ih) (λx. λy. λr. λih. ⋆) m
  ```

- β holds on the nose; closed computations discharge by `⋆`.
- No generativity: signatures compare structurally — two textually
  identical `data` literals define THE SAME type.
- Induction-induction (sorts indexed by other sorts) and recursive
  equation constructors are supported; for IH-bearing coherences, prove
  the twin equation as a standalone lemma first and pass `⋆`.

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
- A Σ-CODE binds over a code, a Σ-TYPE over `El` of one:
  `((m : Int) ⨯ Id Int m m)` is a code, `((e : El NZ) ⨯ Prf p) ⊎ …` is a
  type. Writing `El` in code position silently drops the binder and the
  error is `unknown name 'm'` at the USE, several lines away.
- `class a ≡ class b` is discharged automatically only when the
  quotient's relation is `∥𝟙∥`-shaped or an equation. For any other
  Ω-valued relation (a squash, a conjunction, a variable) SUPPLY the
  witness: `⋆ h`, not `⋆`. The failure otherwise is a bare
  `class x ≐ class y` obligation with no hint.
- A `quot-elim` whose method is an explicit proof term (not `⋆`) owes
  an equation BETWEEN PROOF TERMS as its own well-definedness goal;
  name `prop.irrel` in `using`, or the engine finds a route the kernel
  rejects — and whether it does is store-dependent.
- `transport`'s family is `El A → 𝕌`; for one landing in `Ω` use
  `transportP`. The wrong choice is reported as
  `λ checked against a non-Π type`.
- A calc-chain step whose justification would rewrite inside a
  `quot-elim` scrutinee fails at replay; the same proof written with
  explicit `trans` goes through, because a lemma application is
  unconstrained by position.
- `class X ≐ class Y` does NOT follow from `X ≐ Y` by a lemma:
  class-congruence accepts only STEP-FREE evidence (the component's type
  is not recoverable there). Name the congruence —
  `cong A (λw. Q) (λw. class w) X Y h` — as `realSeq.realEqOfSeqEq` does.
- A calc chain runs with an EMPTY Σ-scope, so a link needing a
  conversion licensed by the item's `using` clause fails — with the same
  symptom as the next bullet, an obligation that IS the link supplied.
  The identical proof written as one `equality.trans` goes through: a
  lemma application is unconstrained by position or scope.
- Greek letters are not identifier characters. `(φ : T)` is a parse
  error reported at the FOLLOWING binder. Use `phi`.
- **Licenses are not monotone.** Citing more `.eq` can UNDO a proof:
  the `.eq` unfolds the GOAL into elim-vocabulary while store lemmas
  are held in SigVar-vocabulary, so links stop matching. Symptom: a
  chain step reports a bare `LHS ≐ RHS` obligation that IS, literally,
  the statement of the link you supplied. Suspect the `using` clause,
  not the link. When automating "add what the hint names", add ONE at
  a time and revert any that does not strictly reduce the obligation
  count — hints list what a route could use, not what this proof needs.
- Prefer the spelling that needs no license. `dbl K` costs
  `ratHalf.dbl.eq` (which then poisons the next step); `S (K + K)` is
  the same term and costs nothing.
- `+` recurses on its SECOND argument: `c + S Z` reduces to `S c` and
  `n + Z ≐ n` is definitional, but `S Z + c` is stuck and `Z + n ≡ n`
  is the lemma `zeroPlusId`. Pick the reducing order when you get to
  choose.
- A conversion the kernel will not replay can often be side-stepped
  with `transport`: it is the identity function, so it inserts nothing,
  but its SIGNATURE does the retyping and the conversion was already
  discharged once at an abstract motive. This is how `realSeq.rseqEq`
  reads one sequence's regularity witness at the other's type.

## Where to look things up

- `docs/NovaFoundation.txt` — the theory, sole source of truth; every
  rule is named and those names are cited in code comments.
- `docs/NovaElaboration.txt` — surface syntax and the discharge engine.
- `docs/NovaKernel.txt` — certificates and approximations (A1–A6).
- `docs/NovaPipeline.txt` — the trust architecture.
- `src/nova/` — the corpus, one topic per file: `nat` (arithmetic),
  `sum` (the disjoint union ⊎: inj₁/inj₂, ⊎-elim, β/η, derived
  injectivity and disjointness),
  `stream` (coinductive streams and conaturals: ν, out, corec,
  β-driven observation lemmas, tlCons by graph-invariant coind),
  `streamEq`/`streamBisim` (observational equality in Ω, bisimilarity
  as the impredicative gfp, bisimReflect — bisimilarity implies
  equality — and the map-id/map-fusion equalities),
  `equality`/`prop` (≡ and Ω), `quotient`/`quottyuniv` (quotients),
  `vect`/`vectAppend` (𝕌-indexed families), `qiitNat`/`qiitBag`/
  `qiitQuot`/`qiitVec` (QIIT basics), `id` (the identity family —
  structural equality as a small QIIT, with ≡-bridges), `qiitInt`
  (recursive equations),
  `qiitConTy` (induction-induction), `qiitCross` (definitions built on
  earlier QIITs), `integer*` (a worked development).
- The ℕ → ℤ → ℚ → ℝ tower, in dependency order: `nat`/`natMore`/
  `natOrder` (arithmetic, monus/max/exp, ≤), `integer*`/`intOrder`/
  `intAbs` (ℤ and its magnitude), `rational`/`rationalQ`/`rationalOrder`
  (ℚ and its sign-based ≤), then `ratBound` (two-sided bounds `Bnd b u`
  — the absolute-value-free primitive everything else is stated in),
  `ratAbs`/`ratMax` (|·|, max, min, each characterised by a
  least/greatest property), `ratLt` (strict <), `ratHalf` (the halving
  law 1/(2n+2)+1/(2n+2) = 1/(n+1)) and `ratArch` (the Archimedean
  property, and `leQOfArch`: "≤ b + 1/(k+1) for every k" collapses to
  "≤ b").
  ℝ is Bishop's regular sequences: `real` (the carrier), `realNeg`,
  `realAdd` (doubled sampling), `realEq` (REq is an equivalence),
  `realOrder` (≤, Ω-valued so it descends by propext), `realAbs`,
  `realLattice`, `realLt`, `realGroup`, `realMetric`. Rule of thumb
  learned there: an operation that is 1-Lipschitz on ℚ lifts
  POINTWISE; one that is not (+) must sample at doubled indices, and
  any relation that is not must be repaired by `leQOfArch`.
  `realSeq` is the bridge `uip.nova` opened: order verdicts are unique
  (`ratBound.leQIsProp`), hence so are regularity witnesses, hence
  `RSeq` is a SET whose equality is equality of the sequence
  (`rseqEq`). Use it when you need to reason about representatives —
  notably `wdOuterOfComm`, which gets a binary operation's outer
  well-definedness free from its inner one plus commutativity.
- `python3 tools/render-specs.py` renders the specs to navigable HTML
  (`build/docs/specs.html`); `--check` cross-checks rule names against
  the sources.
