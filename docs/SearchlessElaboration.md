# Searchless elaboration — the case, the numbers, the bargain

The third document of a trilogy: `PerfNotes.md` records where the time
goes, `ProvingFeedback.md` where the fragility is. This one argues a
design position from both, in two parts. Part I: the discharge
engine's *search* — the store-driven part of the ↓ loop — should be
replaced by operator-supplied direction, and what remains automatic
should be exactly the deterministic, store-independent part. Part II:
the other factor of the conversion cost, δ-transparency, should fall
to the same knife — definitions compute by their clause equations and
never unfold, so goals stay in the vocabulary the operator wrote.
Nothing here is normative; it is a proposal argued from measurements
and experiments on the current corpus.

The framing question, stated once: the elaborator has no prior over
the lemma store — every candidate is as likely as every other, at
every conversion, forever. The *operator* of the surface language
knows, for each equation, which lemma justifies it, in which
direction, and usually at which position. The operator is expected to
be an AI (the language stays human-readable, but generation
effectiveness is the constraint that binds). So "terse" is not the
metric. The metric is: the operator generates quickly, makes few
mistakes, and gets feedback it can act on. Wordy-but-deterministic
wins over terse-but-oracular under that metric — *if* the wordiness is
information the operator already has.

---

## 1. What the search actually is

All of it lives in the ↓ judgements (`NovaElaboration.txt`, step 7 of
the conversion loop; `Nova/Elaboration.idr`). Four mechanisms, of very
different character:

1. **Computation** — whnf by β/δ/El-decoding. Deterministic, not
   search, and not at issue.
2. **Rewrite normalization** (`rwNfElemS`/`rwNfTyS`, `rwFuel = 40`):
   both sides of *every* conversion, plus the equation's type, are
   normalized to a fixpoint against the whole candidate store — every
   accepted lemma of the import closure plus the reflected hypotheses
   of Γ, strictly-shrinking rules first, each candidate attempted at
   every subterm position, full restart after every hit. This runs
   unconditionally, even when the sides are already β-equal: the
   cheapest possible conversion still pays one full failed
   candidates × positions scan per side.
3. **Whole-equation match and transitivity hops** (`candMatchC`,
   `spDepth = 3`): every candidate tried in both orientations against
   the goal by first-order matching; unbound parameters completed as
   nested (budgeted) side-condition searches; failing all that, every
   "hop" candidate may rewrite one side wholesale and the loop
   recurses with the budget decremented.
4. **Congruence descent** (`spCongC`) — same-headed sides compared
   componentwise, each component re-entering mechanisms 2–4
   speculatively.

Mechanism 1, plus hypothesis reflection (silent induction hypotheses,
let-transparency, QIIT coherences), plus proof irrelevance and
injectivity decomposition, is what `ProvingFeedback.md` §I praises —
the extensionality dividend. None of it consults the store. Mechanisms
2–3 are the search this document is about.

## 2. The numbers

Measurement setup: three labels added inside the speculative engine
(`rwnf-elem`, `rwnf-ty` around the rewrite fixpoints; `sp-match` /
`sp-struct` / `sp-cong` around the three alternatives of
`spEqElemC`'s slow path), same `NOVA_PROFILE=1` scaffolding as the
existing `engine`/`kernel`/`cands` labels. Caveat for readers of the
raw dump: hops recurse into `spEqElemC`, so the slow-path labels are
cumulative-inclusive and overlap; `rwnf-elem`/`rwnf-ty` are leaf
intervals and sum truthfully.

`all.nova` (the whole corpus in one run, accepted; ~17.1s wall
uninstrumented):

| where                                  | time  | calls  |
|----------------------------------------|-------|--------|
| discharge engine total                 | 7.3s  | 18,734 top-level attempts |
| — rewrite normalization, element sides | 4.6s  | 38,976 |
| — rewrite normalization, type sides    | 1.1s  | 17,748 |
| — match/hops/struct/descent (rest)     | ~1.6s |        |
| kernel replay + item check             | 2.1s  | 16,935 + 577 |
| candidate-set assembly                 | 0.7s  | (Σ-part cached) |

So the engine is ~44% of wall clock, and **74% of the engine is the
unconditional store-normalization tax** — mechanism 2, paid at every
conversion whether or not it contributes anything. The trusted gate is
*not* the bottleneck: replay costs a fifth of what finding costs.

The hit rates are the sharper indictment. Of the 38,976
element-conversion entries, 2,260 close immediately (identical
lemma-normal forms — and each of those still paid the full fixpoint
first). 36,716 proceed to whole-equation matching, of which

* **146 succeed at match — a 0.4% hit rate** (36,570 fall through to
  the structural finals);
* 59 succeed at the structural finals (36,511 fall through to
  congruence descent);
* the rest close through descent's components re-entering the loop, or
  fail — failure being the *normal* outcome for the speculative
  sub-calls that hops, propext synthesis and side-condition completion
  spawn.

Each of those 36,716 failing-or-succeeding match attempts scanned the
candidate set (average 64 entries on this corpus, ~90 in the ℚ
modules) in both orientations, plus the hop expansion. On the order of
five million candidate matches, to license 146 equations.

Two structural facts make this worse than a constant factor:

* **Cost scales with the library, not with the proof.** Every
  conversion is O(|store| × |term| × fuel), and the store grows
  monotonically with the development, so per-item cost grows with
  everything before it. `PerfNotes.md` measured the superlinear curve
  in `rationalQ` directly (items free at position 5 cost 0.05–0.3s at
  position 50), and the head-symbol-index experiment showed indexing
  does not fix it: the filter keeps 46% of candidates, because
  δ-expanded eliminator spines all share head symbols. The scan is
  inherent to prior-free search over this term language, not an
  indexing bug.
* **The search is not computationally robust.** `ProvingFeedback.md`
  B-3/B-5/B-8 and C-3: matching is first-order and type-blind; whether
  a `⋆` closes depends on the full store, its order, the import list,
  and on whether *unrelated items failed*; a module accepted
  standalone broke when imported next to a sibling because a
  shape-generic lemma fired first and `attemptE` takes one shot —
  on replay failure it never retries with a different candidate.
  Scoping the store to the import closure (commit `cfc3142`) contained
  the blast radius; within a closure, acceptance is still not a
  function of the proof text.

## 3. The two ends of the corpus, and the surprise

The corpus already spans the whole spectrum the tradeoff lives on.

**The terse end** — `qiitNat.nova`, `eqNat.nova`, the clausal defs:
`⋆` in every case, induction hypotheses firing silently through
hypothesis reflection. Elaboration cost ≈ 0 (qiitNat: sub-millisecond
engine time). Crucially, what closes these is *computation plus
reflected hypotheses plus the generated clause lemmas* — the
deterministic mechanisms — not the store search.

**The explicit end** — `integerMul.nova`'s `assocRep`,
`rationalAlgInv.nova`, `rationalQ.nova`: thirty-line `trans`/`cong`
chains for five real steps, every midpoint spelled twice (E-2).

The measured surprise: **the explicit style does not buy back the
search cost.** `rationalAlgInv` — the most explicit file in the corpus
— is also the most expensive (7.1s engine over 15,360 attempts,
~460µs per conversion, against `integerMul`'s 31µs). Every link of an
explicit chain still pays the full store-normalization scan on both
sides, because the engine has no way to know the author already
supplied the justification. Cost tracks term size × store size, never
proof style. The verbosity buys robustness — each link is a small,
locally-checkable goal, which is why the style was adopted — but zero
speed.

And the current corpus is the worst of both worlds in a subtler way:
**the engine's search heuristics leak into the surface text.**
`integerMul.nova` opens with lemmas that exist only because rewriting
is oriented (`distribBack`, `distribBackR` — C-1's flipped copies) and
because permutative lemmas never rewrite (C-2's ~fifteen lemmas whose
only content is a permutation). The comments in that file explain
rewrite orientation to the reader. The operator had to model the
engine's strategy to write acceptable input — which is the strongest
evidence for the framing thesis: the knowledge of which point in the
space is relevant already sits with the operator, and the language
gives it only two dialects, "search everything" (`⋆`) and "here is
everything, but search anyway" (chains).

## 4. Scoring the dialects against the real metric

For an AI operator, per the framing: generation speed, error rate,
feedback quality.

* **Bare `⋆`** — generation trivial; mistakes invisible until a late,
  non-local, core-syntax failure (B-3 misfires, G-1 raw-core dumps,
  C-4 δ-normalized obligation statements); and the feedback *loop
  itself* degrades superlinearly as the library grows, since every
  rerun pays the whole store scan.
* **Explicit chains** — every repeated midpoint is a token-level error
  opportunity, and a mismatch surfaces as an alien conversion
  obligation rather than "link 3's rhs ≠ link 4's lhs"; the `_`-hole
  solving rules must be modeled by the generator (E-1: a `⋆`-shaped
  argument pins nothing); and it is still slow (§3).
* **What both lack** — a way to say the one thing the operator knows
  and the engine does not: *which lemma, which direction, where*.

The information-theoretic sweet spot is: **the operator names the
path; the elaborator checks it deterministically.**

## 5. The bargain

Five moves, in decreasing order of leverage. The line they all draw:
*judgemental-by-construction content stays silent; content-bearing
lemma use is named.*

### 5.1 Keep the deterministic core exactly as is

Computation, hypothesis reflection (silent induction hypotheses,
let-transparency, coherence hypotheses), proof irrelevance, injectivity
decomposition, and the generated defining-equation lemmas (clause
lemmas, QIIT path lemmas — the spec already describes them as
computation "pre-applied", the make-the-trace-directly-matchable
remedy). These are store-independent or hypothesis-scoped,
deterministic, and are everything §I of `ProvingFeedback.md` says
works well. The terse end of the corpus (§3) is untouched by
everything below.

### 5.2 A calc-chain form with named justifications

E-2's suggestion, promoted to the primary proof syntax for equational
content:

```
x  ≡⟨ lemma a b ⟩       y
   ≡⟨ sym (lemma2 c) ⟩  z
```

Each midpoint stated once; each link carries its justification as an
ordinary element of the equality's `Prf` type, elaborated and then
*reflected* — so a link is checked by computation plus that one
equation, candidate set of size one plus hypotheses. Generation is
linear: at every step the operator needs only the lemma name and the
next midpoint, both of which it has. Errors are local: "link 2 does
not close" with a small goal, instead of a δ-expanded composite.
Elaboration cost is O(proof), independent of the library. The kernel
story is unchanged — links materialize the same `Step`s the engine
emits today, just without the search that finds them.

This deletes the bulk of `assocRep`-style chains (the `trans`/`cong`
scaffolding and the doubled midpoints) *and* most of the 5.6s
normalization tax.

### 5.3 Scope `⋆` with `using`

Already in the spec's Future work as "`using <lemma>` hints for
deterministic discharge". `⋆ using (plusComm, distribBack)` sets the
candidate store for that site to: the named lemmas + hypotheses + the
generated defining equations. A bare `⋆` gets the same set minus the
named lemmas. The corpus says this costs almost nothing to demand:
the global store's whole-equation match fired **146 times in the
entire corpus** — those sites gain one `using` clause each. Sites like
`intRRefl` (whose goal *is* `plusComm`) become `⋆ using plusComm` —
which is also better documentation than the bare `⋆` ever was.

### 5.4 Demote global search to advisory

Do not delete the searcher — invert its role. When an obligation is
about to be assumed, run today's match/hops machinery *once, at report
time*, and print its finding:

```
[1] (n : ℕ) ⊢ plus n Z ≐ n : ℕ
    at: vappend_nil, line 14 (checking ⋆)
    hint: closes with plusZeroId (flipped)
```

Search as feedback rather than as acceptance criterion is exactly what
an AI operator wants from the elaborator. Acceptance becomes
deterministic, order-independent, and local — killing B-5, B-8 and C-3
outright, and making B-3 impossible (a named lemma that fails replay
is a local, attributable error at its `using` site) — while the
discovery value of the search is kept, moved to the one place where
its cost is paid once instead of at every conversion.

### 5.5 One real decision procedure: AC-normalization

C-2 already calls this the highest-leverage fix. Permutative goals are
precisely where prior-free search is *provably* useless (oriented
rewriting excludes permutative equations by termination; whole-equation
match cannot chain them without hops exploding) and where the manual
chains are longest — fifteen corpus lemmas whose only content is a
permutation, and a seven-factor permutation that was only tractable by
a change of problem (D-2). For operators *declared*
commutative-associative, normalize both sides modulo AC and emit the
kernel steps that witness the permutation. Terminating, predictable,
prior-free because the fragment is decidable: "computationally robust
search" in the exact sense the framing demands. The dormant
`Solver.CommutativeMonoid` modules are the natural seed; the open
design question is only certificate emission (a permutation witnessed
as a sequence of comm/assoc `Step`s — bounded, mechanical).

## 6. What this costs

* **The prepend-and-rerun loop gains one edit.** Today, proving the
  prepended lemma silently discharges the surfacing site on rerun via
  the store; under 5.3 the site must also say `using <lemma>` (or the
  chain link must name it). One extra, mechanical edit per discharge
  cycle — made by the operator that just wrote the lemma and therefore
  knows its name — and the file becomes a self-contained record of
  *why* it is accepted, rather than a bet on the store's state.
* **Corpus migration.** ~146 match sites gain a `using`; the
  permutation-lemma inventory dissolves into 5.5; the big chains
  *shrink* under 5.2. No file gets longer except by `using` clauses.
* **What is genuinely lost:** serendipitous discharge — a lemma the
  operator did not know applies, applying. 5.4 preserves exactly this
  as a hint instead of an acceptance.
* **Trust:** unchanged. The kernel replays certificates as before
  (`NovaPipeline.txt`); every mechanism above only changes how steps
  are *found*, never how they are believed.

## 7. Alternatives considered and set aside

* **Indexing the scan** — measured, no win (`PerfNotes.md`,
  head-symbol index): the candidate shapes are not discriminating, and
  rejecting a candidate was already cheap. The scan's cost is its
  existence, not its constant.
* **E-graph closure of the store** (Future work in
  `NovaElaboration.txt`) — raises discharge *completeness*, i.e. makes
  the oracle stronger, at the price of making acceptance even less
  predictable and the per-conversion cost higher. It moves in the
  opposite direction from every finding above; if pursued, it belongs
  in the advisory layer (5.4), where completeness is pure upside.
* **Memoizing conversions** — helps constants (the two normal-form
  memos already landed, 2.5× and 2×), cannot help the store-scaling
  law or the robustness failures, both of which are about *what* is
  searched, not how fast.

## 8. Summary (part I)

44% of wall time is prior-free search; three quarters of that is a
normalization tax paid at every conversion regardless of need; the
match layer that justifies the tax fires at 0.4%; cost grows with the
library rather than the proof; and acceptance is not a function of the
proof text. Meanwhile the operator — measured by the corpus it was
forced to write — already possesses the direction the engine is
searching for, and today can express it only by modeling the engine's
own heuristics. The bargain: keep the deterministic dividend (§5.1),
let the operator say what it knows (§5.2, §5.3), move discovery to
report time where it is paid once (§5.4), and spend real automation
budget only where the problem is decidable (§5.5). Wordier at ~150
sites, shorter everywhere chains live, deterministic and
module-local everywhere.

Part II below adds the second axis: the store is one factor of the
per-conversion cost, and δ-transparency is the other — and the second
turns out to be the larger one in the heavy modules.

---

# Part II — the cost of lost abstraction

The question, posed against the ℚ development: very few theorems about
`+` need to know that `+` *is* an `ℕ-elim`. Does keeping every
definition δ-transparent to the engine's normalizer at all times incur
a real cost? Would it be worth assuming `+` exists and taking its
computation rules propositionally — or scoping δ the way §5.3 scopes
the propositional store?

The answer, in one line: δ-transparency is the *size* factor of the
cost model, it is ~8× in the ℚ stack, and the right replacement is
neither propositionalization nor demand-driven unfolding but
**computation by the clause equations** — a mechanism the system
already half-contains.

## 9. Measured: the blowup, and the cost model it completes

At every conversion the engine deep-normalizes both sides
(`betaElem`), which δ-expands **every** definition occurrence —
including stuck ones, where unfolding provably cannot progress:
`n * m` with `m` a variable becomes a stuck `ℕ-elim` spine, strictly
larger, no further reduction available, and never folded back. Sizes
at the top-level conversion sites (`sz-att-in` / `sz-att-nf` labels,
same scaffolding as §2):

| file            | avg goal size as written | after forced δ/β | blowup |
|-----------------|--------------------------|------------------|--------|
| nat             | 13                       | 13               | 1.0×   |
| integerMul      | 35                       | 51               | 1.5×   |
| intNonZero      | 33                       | 258              | 7.9×   |
| rationalQ       | 35                       | 301              | 8.5×   |
| rationalAlgInv  | 32                       | 260              | 8.1×   |
| all.nova        | 30                       | 219              | 7.4×   |

The blowup compounds with abstraction-stack height (ℚ → Rat → ℤ → ℕ:
each level's definitions expand into the level below's eliminators),
so it only worsens as a library deepens. And it completes the cost
model: **per-conversion cost ∝ nf-size × store-size** fits the data
almost exactly — rationalAlgInv vs integerMul is 15× per conversion =
5.4× size ratio × 2.4× candidate-store ratio. §5's `using` attacks the
store factor; this part is about the size factor, which in the ℚ
modules is the bigger of the two. Eliminating it alone projects the
7.3s engine to roughly 1–1.5s.

It also explains a §7 result: the head-symbol index failed *because*
of δ-transparency — expansion makes every hot term
`ℕ-elim`/`quot-elim`-headed, destroying exactly the discrimination an
index needs. Folded terms are `plus`/`intMul`-headed and discriminate
fine.

## 10. Propositionalization, tested — and rejected

The literal form of "assume `+` and its rules propositionally" is the
spec's own e-decl abstract-interface idiom, so it can be run today. A
25-item corpus (nat.nova's equational theory plus integerMul's
explicit ℕ block, `assocRep` included) was elaborated twice: once over
the transparent definitions, once over

```
def + : ℕ → ℕ → ℕ                                    -- declaration
def plusZeroId : (n : ℕ) → n + Z ≡ n ∈ ℕ             -- declared, enters E
def plusSucId  : (n : ℕ) (m : ℕ) → n + S m ≡ S (n + m) ∈ ℕ
def * : ℕ → ℕ → ℕ
def multZeroId : (n : ℕ) → n * Z ≡ Z ∈ ℕ
def multSucId  : (n : ℕ) (m : ℕ) → n * S m ≡ n + n * m ∈ ℕ
```

Result: the abstract version is **slower** (engine 68ms vs 40ms — at
blowup 1.0× there is nothing to win on size, and a propositional step
costs a candidates × positions scan where β costs a traversal), and it
**loses three proofs**, with one crisp common cause: the S-cases of
`sucMult`, `multDistrib`, `multAssoc` all need
`n * S m ⇝ n + n * m` at an *inner* position — and that defining
equation is **size-increasing**, so the terminating rewriter may never
fire it, while hops fire growing candidates only at the root. β is
directional *growth*; terminating rewriting cannot simulate it.
(Closed evaluation survived — `2·3` and `3·4` closed through the hop
layer — the casualties are precisely the open inductive cases where
today's engine is silently strong.)

So full propositionalization trades a cheap, complete, growth-capable
mechanism for an expensive, orientation-restricted one. Wrong tool.

## 11. Demand-driven δ, and the one-step objection that kills it

The obvious refinement — unfold a definition only when an argument's
constructor lets a reduction happen — fails to a decisive objection:
**it preserves abstraction for exactly one step.** Unfold
`plus n (S m)`, take the ι-step, and the result is not
`S (plus n m)` but `S (ℕ-elim … n (n ih. S ih) m)` — the definiens
spliced in, the recursive occurrence naked. Recovering the folded form
means *refolding*: syntactically recognizing the definiens spine and
folding it back, which is Coq's `simpl`-refolding — fragile guesswork
against arbitrary bodies, and rightly notorious.

## 12. The resolution: compute by the clauses, never by the definiens

The system already contains the artifact that dodges refolding
entirely. A clause lemma —

```
plusS : (m : ℕ) (n : ℕ) → plus (S m) n ≡ S (plus m n) ∈ ℕ
```

— is one ι-step of the function's operational behavior **with the
refolding already done, at definition time**: the elaboration spec
guarantees its right-hand side stays in the abstraction's vocabulary
("recursive occurrences in tᵢ stay REFERENCES to f"). So the mechanism
is not "unfold on demand" but "**never unfold; step by the clauses**".
The definiens (the `ℕ-elim` body) exists to witness existence and
uniqueness for the kernel; the engine's operational semantics for a
defined name is its clause set. Abstraction is then preserved to
arbitrary depth: `plus n (S m)` steps to `S (plus n m)` and the
definition never opens.

What blocked this in §10 was the rewriter's size restriction. But a
clause differs from an arbitrary growing lemma in one structural way:
**its LHS pattern demands a constructor**, so every firing consumes
one — it fires only where an ι-redex exists, and terminates for the
same reason the recursor does.

Tested, as a one-clause change to the candidate classifier
(`orderedParts` in `Nova/Elaboration.idr`, flagged as experiment): a
CLAUSE-SHAPED candidate — SigVar-headed application spine with a
constructor-headed argument — is admitted as a rewrite rule regardless
of size. Results:

* **Abstract variant:** all three lost proofs close; the only open
  entries are the six intentional declarations. Closed evaluation
  closes too. Full parity with the transparent version, with `+`/`*`
  never unfolded — they *have no bodies at all*.
* **Full corpus:** still `Accepted.`, timing unchanged. Corpus-neutral
  where transparency exists, completeness-restoring where it does not.

The engine's normalizer under this design: β for the primitives
(λ-redexes, eliminators at constructors, El-decoding) **plus
clause-steps for defined names, minus δ for any def that has
clauses**. Nothing refolds because nothing unfolds. This is what makes
§9's 8× reachable: `intAdd x y` stays a three-node folded spine when
stuck, and applied to `class`-constructors it steps by its
characteristic equation to a `class`-result — still in vocabulary —
instead of δ-exploding into a `quot-elim` spine.

## 13. What the clause-driven design demands, honestly

1. **Every definition needs interface equations.** Clausal defs and
   QIIT-generated names have them for free. Eliminator-defined
   functions (`intAdd`, `qInv`, …) need their characteristic equations
   at constructors (`intAdd (class a) (class b) ≡ class (…)`) —
   auto-derivable for eliminator-shaped bodies (one β-step, provable
   by `⋆`), and already written by hand in the corpus where it hurts
   (`qInvCls`, `vectZ`/`vectS`). A raw λ-definiens with no clauses
   stays transparently δ: the legacy tier.
2. **The type side leaks less than feared, but not zero.** `e-app`
   needs `whnf(C) = Π`; when `C = El (vect (S n) a)` the `vectS`
   clause fires clause-wise, abstraction intact. Only non-clausal
   type-valued defs still need head-δ, and the exposed former is
   consumed by the judgement rather than spliced into goals.
3. **The kernel is untouched.** It keeps full δ — the conservative
   direction: clause-steps are ordinary store-lemma steps in the
   certificate, and anything the weaker engine normalizer equates, the
   kernel's stronger one confirms. Trust story unchanged.
4. **Scoped transparency remains as the escape hatch**: an
   `unfolding (f, g)` annotation — the β-side twin of `using` — for
   the rare proof genuinely *about* an implementation. And
   ProvingFeedback D-3 ("keep representatives abstract; instantiate by
   application"), the most reliable manual technique found, is
   precisely this design done by hand; it becomes automatic.
5. **Not yet demonstrated:** the performance half end-to-end. The
   experiment proves the completeness half (clauses fully replace δ at
   ℕ level). Actually withholding δ in `betaElem` for defs-with-clauses
   and re-running the ℚ stack is a larger surgery (the normalizer must
   consult clause sets; engine/kernel FBeta finals stay aligned because
   the engine is strictly weaker). The projected ~8× rests on §9's
   measured sizes plus the validated cost model, not on a run.

A closing convergence with part I: this erases the artificial line
between "computation" and "the store" for defining equations. A
definition's clauses are simultaneously its operational semantics
(fire at constructor demand, silently — computation) and its interface
in the store (fire by name at stuck occurrences — reasoning). One
artifact, two firing conditions, no definiens in sight either way. The
two factors of the cost model then fall to the two halves of the
design: `using`/chains bound the store factor (part I), clause-driven
computation bounds the size factor (part II), and per-conversion cost
approaches O(written proof) in both dimensions.

## 14. Status: the bargain, landed

Part I's moves have shipped (see git history on this branch): §5.2 calc
chains; §5.3 as `using` clauses at item and ⋆ level, with the corpus
fully migrated (156 clauses) and the SCOPED DISCHARGE now the default
semantics of `docs/NovaElaboration.txt` (NOVA_GLOBAL_STORE=1 is the
migration escape hatch); §5.4 as the report's `hint:` line. Measured on
the corpus: unannotated 33.6s wall / 20.7s engine → annotated, scoped
12.8s / 0.52s — the store factor is retired and per-conversion cost
tracks the named set, so the superlinear curve of §2 is gone
structurally. §5.5 (AC) and Part II (clause-driven normalization, the
size factor) remain open; what is left of the engine time is almost
entirely §9's δ-blowup.

## 15. Experiment inventory

Everything below is measurement scaffolding or experiment, not design
commitment; all of it is inert without `NOVA_PROFILE=1` except the
classifier change, which the full corpus regression covers.

* Profiling labels in `Nova/Elaboration.idr`: `rwnf-elem`, `rwnf-ty`
  (rewrite-fixpoint leaf time), `sp-match`/`sp-struct`/`sp-cong`
  (slow-path alternatives; cumulative-inclusive under hop recursion),
  `sz-att-in`/`sz-att-nf` (top-level goal sizes, written vs
  normalized).
* `orderedParts`: clause-shaped growing candidates admitted as rewrite
  rules (§12), marked with an EXPERIMENT comment.
* The propositionalization A/B (`transNat.nova` / `absNat.nova`:
  identical 25-item body over transparent defs vs declarations +
  declared computation rules) lives in session scratch; it is
  reproducible from §10's header sketch plus nat.nova's lemma set and
  integerMul.nova's pure-ℕ block verbatim.
