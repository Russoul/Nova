# Nova, hands-on — a two-hour session for software engineers

**Thesis.** Nova is a proof assistant with *extensional* equality: an
equation you have in hand is a fact the type checker uses, not a value
you carry around and cast with. That single design decision removes
the plumbing (`subst`, `cong`, `rewrite`, setoids, bisimilarity
relations, funext postulates) that makes Agda, Lean and Coq feel
unlike pen-and-paper mathematics — and, for engineers, it is what
makes *correct-by-construction executable code* look like the code you
would have written anyway.

**Audience.** Functional programmers (Haskell); has heard of Agda and
Lean; no proof-assistant experience assumed.

**Format.** Live coding in the editor, on the files in `start/`. The
audience follows along on their own machines (see *Setup*) or watches.
Every Nova snippet in this session is real and checked: the finished
versions are the top-level `*.nova` files here, and `./check.sh`
verifies both them and the live starting points.

---

## Files

| file | part | what it is |
| --- | --- | --- |
| `start/Arith.nova` → `Arith.nova` | 1 | ℕ, `plus`, `times`; holes, induction, chains, licences |
| `start/Vect.nova` → `Vect.nova` | 2 | length-indexed vectors: safe `vhead`, `vappend`, `vzip`, `vreverse` — coercion-free |
| `start/Equality.nova` → `Equality.nova` | 3 | the J-toolkit as one-liners, funext as a theorem, program equivalence as equality, `≡-elim` |
| `start/Bag.nova` → `Bag.nova` | 4 | multisets as a quotient type: order-independent reducers, enforced |
| `start/Stream.nova` → `Stream.nova` | 5 | streams: `map id s ≡ s` by coinduction, and it rewrites |
| `agda/*.agda` | 1–5 | the Agda counterpart of each comparison (not machine-checked here; see `agda/README.md`) |
| `check.sh` | — | `nova elab` on everything: finished files must be *Accepted*, start files may only have holes/obligations |
| `slides.html` | 0–6 | the slides: thesis, the loop, one Nova-vs-Agda comparison per part, the price, cheat-sheet (open in a browser; arrow keys) |

Imports resolve against `nova.root` in this directory, so `start/Vect.nova`
imports the *finished* `Arith.nova` — each part builds on the previous
part's completed library.

---

## Setup (before the session)

```bash
pack build nova.ipkg && pack build nova-lsp.ipkg     # from the repo root
cd presentation && ./check.sh                        # everything ok?
```

Editor: VS Code with the `russoul.nova` extension, or neovim with
`editors/nvim` (both installed via the flake; see the repo README).
The server re-checks **on save** — every "save" below means "save and
look at the diagnostics". In VS Code: hover a `?hole` for its goal;
`Cmd-.` on a hole for the *eliminate* code actions; the Problems panel
lists obligations (errors) and holes (warnings), each with its `hint:`.

Typing the symbols: every Unicode token has an ASCII fallback and they
mix freely — `->` `\x` `:=` `==` `\` `\star` `\<` `\>` `Nat` `Set`
`Prop` `Nat-elim` `\in` `||` `\nu` `\X` `inj1` `.1`. Type ASCII live;
`build/exec/nova distill file.nova out/` prints the canonical Unicode
form afterwards (and proves the round trip). Have a large font: the
goals are wide.

Terminal fallback if the editor misbehaves: `build/exec/nova elab
start/X.nova` prints the same report, and `build/exec/nova eliminate
start/X.nova LINE:COL VAR` is the code action.

Open in tabs before starting: `start/Arith.nova`, the corresponding
`agda/*.agda` files, and `docs/NovaFoundation.txt` (for the one time
someone asks "where is the rule").

---

## Timeline (120 min)

| min | part | mode |
| --- | --- | --- |
| 0–10 | 0. What Nova is; the loop | slides / talk |
| 10–35 | 1. Primer: ℕ, holes, induction | live |
| 35–60 | 2. Correct by construction: vectors | live |
| 60–65 | break | |
| 65–80 | 3. Extensional equality, concretely | live |
| 80–100 | 4. Quotients: reducers that must commute | live |
| 100–112 | 5. Streams: equality of infinite behaviour | live (shorter if late) |
| 112–120 | 6. The price, and Q&A | talk |

Parts 3 and 5 are the ones to compress if time runs short; part 2 and
part 4 carry the thesis.

---

## Part 0 — What Nova is (10 min, talk)

Say, roughly:

* A proof assistant is a type checker for a language in which
  propositions are types and proofs are programs. You already know the
  language: it is Haskell with dependent types and no partiality.
* Agda, Lean and Coq are **intensional**: `a ≡ b` is a data type; a
  proof of it is a value; to *use* it you transport along it
  (`subst`, `rewrite`, `cong`). Two functions with the same graph are
  not equal. Two streams with the same behaviour are not equal. Two
  bags with the same elements are not equal unless you build a
  quotient by hand.
* Nova is **extensional** (Martin-Löf's ETT, mechanised): `a ≡ b` is a
  *proposition* (a type in Ω with at most one inhabitant, written ⋆), and
  a hypothesis `h : a ≡ b` is **reflected**: wherever `h` is in scope,
  `a` and `b` are interchangeable for the type checker. Function
  extensionality, proof irrelevance, uniqueness of equality proofs,
  quotients with judgemental computation, and coinductive equality all
  follow, as theorems or as rules — no axioms, no cubical machinery.
* The price is that type checking is undecidable in general. Nova's
  answer is the workflow you will see all session:
  1. you write a program or a proof;
  2. where the elaborator needs an equation it cannot see, it does not
     fail — it records an **obligation** and carries on;
  3. the report lists obligations and open holes (`?x`), each with its
     context and usually a **hint** naming what would close it;
  4. you close them by *citing* — a `using (…)` clause naming lemmas
     and unfoldings the proof may use, and/or by adding a lemma above;
  5. a file is accepted when zero obligations remain. Everything is
     replayed by a small trusted kernel.
* There are no tactics and no proof search: what a proof cites is
  written in the file (think `simp only [ … ]`, never `simp`). This is
  deliberate — acceptance depends only on the item and what it names.

Then open `start/Arith.nova`.

---

## Part 1 — The primer (25 min, live: `start/Arith.nova`)

**Goal.** The audience can read a `def`, put a hole, run an induction
from a code action, read an obligation, and cite what it asks for.

1. Walk through `plus` and `times`. A def with clauses is a program;
   the clauses are also equations named `plusZ`, `plusS` (hover them).
2. `twoPlusThree ≔ ⋆`. Save. Say: ⋆ is the proof of every proposition
   that holds; there is no `refl`. The report says:
   ```
   [1] ⊢ plus (S (S Z)) (S (S (S Z))) ≐ S (S (S (S (S Z)))) : ℕ
       hint: closes by citing plus.eq
   ```
   Explain: definitions are opaque to a proof unless the proof says
   otherwise. Add `using (plus.eq)` before `≔`. Save: gone.
3. `plusZr … ≔ λn. ?zr`. Hover `?zr`:
   `(n : ℕ) ⊢ ?zr : plus n Z ≡ n ∈ ℕ`. Code action → *eliminate n : ℕ*.
   The hole becomes `(ℕ-elim ?zrZ (n ih. ?zrS) n)`. Hover both:
   `?zrZ : plus Z Z ≡ Z` and, under `ih : plus n Z ≡ n`,
   `?zrS : plus (S n) Z ≡ S n`. Say: the motive was read off the goal;
   nothing was written that the checker would not reconstruct.
   Replace both holes with ⋆, save: two obligations. Cite `plus.eq`
   (the hint on the first names `plusZ`; `plus.eq` covers both).
   **Accepted for this item.** Point out the step case: with `ih` in
   scope, `S (plus n Z)` *is* `S n` — reflection, no `cong`.
4. `plusSr`: the audience does it (same recipe; 2 min).
5. `plusComm`: hover `?base` and `?step`. Write the base as a chain:
   ```
   (plus Z m ≡⟨ plusZ m ⟩ m ≡⟨ plusZr m ⟩ plus m Z)
   ```
   and the step as
   ```
   (k ih. plus (S k) m ≡⟨ plusS k m ⟩ S (plus k m) ≡⟨ ih ⟩ S (plus m k) ≡⟨ plusSr m k ⟩ plus m (S k))
   ```
   Save: **Accepted.** No `using` clause at all: chain links are proof
   terms, and their equations are reflected at the link.
6. Show `plusComm2` in the finished `Arith.nova`: same theorem,
   `using (plusZ.rw, plusS.rw, plusZr.rw, plusSr.rw)` and two ⋆s.
   Vocabulary, once and for all:
   * `x.eq` — the proof may unfold definition `x` (compute with it);
   * `l.rw` — use lemma `l` as a left-to-right rewrite rule anywhere;
   * `l` — use lemma `l` by matching the whole goal (this is how a
     commutativity lemma is used — it would loop as a rule);
   * `hyp.rw` — use the hypotheses in context (e.g. `ih`) as rules.

**Agda alongside** (`agda/Arith.agda`). Same programs; `plusZr` is
`cong suc (plusZr n)`, and the step of commutativity is
`cong suc (plusComm k m)` inside a `trans`. What is gained: nothing
dramatic yet — the *induction hypothesis is a fact, not a value*, so
it is used by being in scope. Say that the difference compounds:
every `cong`/`subst` Agda needs here is one that a longer development
needs a hundred times.

---

## Part 2 — Correct by construction (25 min, live: `start/Vect.nova`)

**Goal.** Executable code whose types do the checking, with arithmetic
in the indices — and the moment where intensional theories make you
put coercions *inside the program*.

1. `data V` — a quotient-inductive-inductive signature; here just an
   indexed family, like Agda's `Vec`. Parameters in brackets; the
   generated names are the sort `V`, constructors `vnil`/`vcons`, and
   two eliminators `VElim` (into types) and `VElimP` (into
   propositions). Show `vhead` (given): the motive sends length `Z` to
   `𝟙`, so the empty case is `()` and can never be selected at `S n`.
   No `Maybe`, no exception.
2. `vappend` (given): its type computes the length, `plus n m`.
3. **`vrevAcc`, live.** Hover `?nilCase`: `⊢ ?nilCase : V a (plus Z m)`
   with `acc : V a m`. Type `acc`. Hover `?consCase`:
   `V a (plus (S k) m)` with `ih : (m : ℕ) → V a m → V a (plus k m)`.
   Type `ih (S m) (vcons a m x acc)`. Save. Two obligations from
   `vrevAcc` (plus one from `reverseTest`, which cannot compute while
   `vreverse` is still a hole, and one on `vappendNil`'s statement —
   ignore those for now):
   ```
   V a m                 ≐ V a (plus Z m)         type   hint: V.eq, plus.eq
   V a (plus k (S m))    ≐ V a (plus (S k) m)     type
   ```
   **This is the slide.** Put `agda/Vect.agda` next to it: in Agda the
   cons case *does not type check* until you write
   `subst (Vec A) (+-suc n m) (rev-acc xs (x ∷ acc))` — a coercion in
   the executable code, which every later proof must push through, and
   which blocks `head (reverse v)` from computing for a variable `n`.
   In Nova the program is the Haskell program; the arithmetic facts
   are obligations *about* it. Cite `plusZ.rw, plusS.rw, plusSr.rw`
   on `vrevAcc` (the hint's `plus.eq` would also close the first, but
   unfolding `plus` hides it from the lemmas that close the second —
   see *Hazards*). Save: one obligation left, for `vreverse`.
4. `vreverse`: `?rev` → `vrevAcc v (vnil a)`. Obligation
   `V a (plus n Z) ≐ V a n`, hint `plusZr`. Cite `plusZr.rw`. Save.
5. `reverseTest` is now Accepted: `vreverse v123 ≡ v321` holds by
   computation — the program *ran* inside the type checker, through
   no coercions. (`build/exec/nova run Vect.nova v321` prints the
   normal form as raw kernel syntax, in unary; fine for a laugh, keep
   it small.)
6. `vappendNilL`/`vappendCons` (given): the two computation rules of
   `vappend` as lemmas — after this nobody needs `vappend.eq`.
7. **`vappendNil`.** Before touching the hole, look at the report: the
   *statement itself* raised
   `V a (plus n Z) ≐ V a n type — hint: closes with plusZr`.
   Say it slowly: `vappend v vnil` has type `V a (plus n Z)`, `v` has
   type `V a n`, and `≡` needs one type. In Agda this statement cannot
   be written; you write it through `subst` or heterogeneous `≅`
   (`agda/Vect.agda`, `++-[]`) and then fight both. Here: one
   obligation, one citation. Then prove it by induction on `v`, at a
   *propositional* motive (`VElimP`, no coherence arguments since
   equality proofs are unique):
   ```
   VElimP a (λk. λu. vappend {a} {k} {Z} u (vnil a) ≡ u ∈ V a k) ⋆ (λk. λx. λxs. λih. ⋆) n v
   ```
   and cite
   `hyp.rw, V.eq, V.unfold, VElim.eq, vnil.eq, vcons.eq, vappend.eq, plusZr.rw, plusZ.rw, plusS.rw`.
   **Accepted.** (Indexed sorts do not yet get the *eliminate* code
   action, so this eliminator is typed by hand; the ℕ one in Part 1
   was generated.)

What is gained, in one sentence for engineers: *the index arithmetic
is checked, and it costs no code.*

---

## Part 3 — Extensional equality, concretely (15 min, live: `start/Equality.nova`)

**Goal.** Make "reflection" tangible: hover each goal, notice what it
already looks like, type ⋆.

1. `sym`, `trans`, `cong`: hover, then ⋆ each. `trans` needs
   `using (hyp.rw)` (two hypotheses chain). Agda: three pattern
   matches on `refl` — J.
2. `subst`: hover — the goal is `P b` and `p : P a` is in scope. Type
   `p`. Say: transport is the identity function; `P a` and `P b` are
   the same type here. In Agda `subst` returns a *new value*, and a
   whole genre of lemmas exists to reason about it.
3. `uip`: `p q : a ≡ b ⊢ p ≡ q` — ⋆. Not provable in general in Agda
   (needs K; false in cubical).
4. `funext`: ⋆; the obligation `f ≐ g : A → B` has no hint — cite
   `pi.eta` (η for functions: compare under the binder, where `h x` is
   reflected). **A theorem.** Agda:
   `postulate`, which blocks computation wherever used, or cubical.
5. `doublesAgree : double1 ≡ double2` — two implementations, one by
   `plus n n`, one by `times 2 n`, equal *as functions* (⋆). For
   engineers: refactoring with a proof. Anything proved about
   `double1` transfers to `double2` by rewriting, since it *is* an
   equality.
6. `learnedLength`: hover — `v : V ℕ n`, `h : n ≡ 3`, goal `V ℕ 3`.
   Type `v`. No cast. Agda: `subst (Vec ℕ) h v`.
7. `pinned`: hover; then type `≡-elim ?g x w` and hover `?g`:
   `⊢ ?g : plus Z Z ≡ Z` — the variable is gone and the goal is
   restated at `Z`. (Reflection already made `x ≐ Z` available; what
   `≡-elim` changes is what you *read*. Note: a hypothesis whose
   left side is a bare variable is never used as a rewrite rule, so
   `⋆` alone does not close this — that is exactly what `≡-elim` is
   for.) Fill with ⋆; `plusZr` is already cited.

---

## Part 4 — Quotients: reducers that must commute (20 min, live: `start/Bag.nova`)

**Goal.** A quotient type in practice; the type checker asking for
order-independence; "this function does not exist".

1. `data Bag`: `nil`, `ins`, and an *equation constructor* `swp`:
   `ins x (ins y m) ≡ ins y (ins x m)`. Not a relation to respect
   later — an equality, now.
2. `oneTwo ≔ ⋆`: the two insertion orders are equal. Save; the hint
   asks for `Bag.unfold` first, and then goes quiet — cite the full
   set `swp, Bag.unfold, ins.eq` (the equation constructor, the data
   type's head, the constructor's unfolding).
3. `size`: hover `?sizeOk` — `S (S ih) ≡ S (S ih)`. Say: a fold out of
   a `Bag` has one extra argument, a proof that the `ins` case does not
   care about order. ⋆.
4. `sum`: hover `?sumOk` — `plus x (plus y ih) ≡ plus y (plus x ih)`.
   The exchange law: `plusSwap x y ih`. **This is the slide.** The
   checker derived the commutativity requirement on the reducer from
   the data type's equation. Map-reduce, CRDT merge, event-sourced
   aggregates: "must not depend on arrival order" is now a type.
5. `first` — "the first element". Hover `?impossible`:
   `(x y : ℕ) … ⊢ x ≡ y`. It asks you to prove that any two numbers
   are equal. This function does not exist; delete it. (In
   setoid-Agda, `first` type checks fine; the bug surfaces only if
   someone remembers to try to prove `first-resp`.)
6. `union` (given), `sumTest`: it runs.
7. `sumSwap`: ⋆ (cite `swp, Bag.unfold, ins.eq`). Compare
   `agda/Bag.agda`: `sum-resp`, six cases by induction over the
   relation, the interesting one being exactly the exchange law —
   *for every function, separately*. Cubical Agda is closer (the swap
   clause is the exchange law as a path) but adds an interval
   variable, a `trunc` constructor with its own clause everywhere, and
   transports that do not compute away.
8. `sumUnion`: induction over the quotient at an equational motive
   (`BagElimP`; no coherence argument). Hover both holes and write
   them as chains over the given computation rules:
   ```
   sum (union (nil ℕ) n) ≡⟨ unionNil n ⟩ sum n ≡⟨ plusZ (sum n) ⟩ plus Z (sum n) ≡⟨ sumNil ⟩ plus (sum (nil ℕ)) (sum n)
   ```
   ```
   sum (union (ins ℕ x r) n)
     ≡⟨ unionIns x r n ⟩ sum (ins ℕ x (union r n))
     ≡⟨ sumIns x (union r n) ⟩ plus x (sum (union r n))
     ≡⟨ ih ⟩ plus x (plus (sum r) (sum n))
     ≡⟨ plusAssoc x (sum r) (sum n) ⟩ plus (plus x (sum r)) (sum n)
     ≡⟨ sumIns x r ⟩ plus (sum (ins ℕ x r)) (sum n)
   ```
   Save: two links complain (they rewrite inside the first argument
   of `plus`); cite `hyp.rw`. **Accepted.** (The hint suggests
   unfolding; ignore it — *Hazards*.)

---

## Part 5 — Streams (12 min, live: `start/Stream.nova`)

**Goal.** Equality between infinite objects, and that it is the same
`≡` as everywhere else.

1. `stream a ≔ ν (K a × 𝕏)`: a coinductive type; `out` observes, `corec`
   builds from a state and a step — every generator/signal/event loop.
   `hd`, `tl`, `iterate`, `nats`, `map`, `evens` (given).
2. `evens2 ≔ ⋆`: `hd (tl (tl evens)) ≡ 4`; cite the hint's list.
   Observations compute.
3. `mapId : map id s ≡ s` — by `coind`. The invariant is given: `u`
   and `v` are related when `u` is `map id w` and `v` is `w` for some
   `w`. Hover `?start` (it holds at the start with `w ≔ s`):
   `⋆ (s, ⋆, ⋆)`. Hover `?step`: heads agree and the tails are again
   related, through `tl w`:
   `squash-elim h (w. ⋆ (⋆, ⋆ (tl (w .π₁), ⋆, ⋆)))`. Cite
   `map.eq, hd.eq, tl.eq, id.eq, hyp.rw`. **Accepted** — an equation
   between two infinite objects.
4. In the finished file: `mapFuse`, same shape, and then `evensFused`
   by ⋆ citing `mapFuse` — the fusion law *rewrites under `map`*,
   because it is an equality. `agda/Stream.agda`: `map-id` is a
   bisimilarity `≈`, and `map-cong` has to be proved before `≈` can be
   used under `map` — once per function, forever. `map id s ≡ s` is
   simply not provable there.

---

## Part 6 — The price, and Q&A (8 min, talk)

Be candid; engineers trust candour:

* **Undecidable conversion** is why obligations and `using` exist. You
  will cite things. The hint usually tells you what; sometimes it
  suggests an unfolding that is worse than a lemma (see *Hazards*).
* **No metavariables/unification** in the elaborator: binders are
  named, motives are written or recovered from the goal, implicit
  arguments are recovered by first-order matching — so occasionally
  you write `{a} {n} {Z}` by hand (as in `vappendNil`).
* **No tactics.** A proof is a term: eliminators, chains, ⋆. What the
  kernel replays is what you see.
* **Young.** One-person project; the corpus in `src/nova/` (ℕ → ℤ → ℚ →
  ℝ as Bishop reals, algebra, codata) is what has been built with it.
  The theory is `docs/NovaFoundation.txt`; the elaborator and kernel
  are specified rule by rule in `docs/`.

Closing line: *in an intensional theory you prove things about your
program and then spend the afternoon convincing the type checker that
the program you proved things about is the one you wrote. Here it is
the one you wrote.*

---

## Cheat-sheet (put on a slide, keep visible)

```
def f : T ≔ t             def f : ℕ → ℕ | f Z ≔ … | f (S n) ≔ …      -- clauses ⇒ fZ, fS lemmas
?name                     a hole: hover for its goal; code action eliminates a variable
⋆                         the proof of any proposition that holds (equality included)
a ≡⟨ p ⟩ b ≡⟨ q ⟩ c        equational chain; p : a ≡ b, q : b ≡ c
ℕ-elim base (k ih. step) n           induction (motive read off the goal)
XElim / XElimP            a data type's eliminators, into types / into propositions
using (x.eq, l.rw, l, hyp.rw, pi.eta, X.unfold)     the licence: unfold x · rule l · match l · rules from hypotheses · η · expose X's head
```

## Hazards (things that bit while preparing this; keep this page open)

* **Licences are not monotone.** Citing `plus.eq` unfolds `plus` in the
  goal into its eliminator, after which lemmas *stated with* `plus`
  (`plusZr`, `plusAssoc`) no longer match. Prefer the clause lemmas
  (`plusZ.rw`, `plusS.rw`) plus the lemma you need; use `x.eq` only
  when the goal is a closed computation. Add citations one at a time.
* **Add licences last.** The report prints goals under the surfacing
  item's licence, so once `plus.eq` is cited the remaining holes in
  that item show `ℕ-elim …` instead of `plus …`. Fill holes first, then
  cite.
* **A bare ⋆ in a QIIT eliminator method** (`BagElimP … ⋆ …`) does not
  pick up cited `.rw` lemmas, while the ascribed form
  `(⋆ : <the goal>)` or an explicit chain does. Use chains there
  (`sumUnion`), or ascribe.
* **Chain links that rewrite inside the first argument of `plus`**
  (its recursive position) need `hyp.rw`; the hint will wrongly
  suggest unfolding instead.
* **`X.unfold` is needed whenever a data type's name must be seen
  through** — implicit-argument recovery on `V a n`, `Bag a`,
  `stream a` fails with "head exposure blocked" otherwise. It is
  harmless to cite up front on definitions; on *proofs* it can change
  which lemmas match (see the first point) — test.
* **Indexed sorts have no eliminate code action** (`v : V a n`). ℕ,
  ⊎, plain QIITs (`Bag`), equations (retype) and pairs do.
* **Obligations are deduplicated by statement**: a second item with the
  same open equation shows nothing new. The count in the final report
  is what matters, not the per-item noise.
* **Chain links are inference positions**: a hole in a link must be
  ascribed, `(?mid : a ≡ b)`. The start files put holes at the case
  level instead.
* If the server looks stale, save again; it checks on save only. The
  status bar shows the last elaboration time.
