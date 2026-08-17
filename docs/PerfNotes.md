# Elaborator performance — measurements

The performance campaign's running record, kept in chronological
order: each section's numbers are wall clock AS MEASURED AT THAT
POINT (macOS/arm64, Chez backend; `pack build` was 15.6s at the
start). Later sections change the code the earlier ones measured —
notes in brackets mark what has since been removed, so the knowledge
keeps its context without dead references.

## Where the corpus stands

`nova elab` per file, slowest first:

```
 72.79  rationalAlgInv      1.87  eqInt
 68.41  rationalEffective   1.13  definingEq
 61.91  intNonZero          0.54  integerMul
 60.34  rationalInv         0.35  intEffective
 37.47  rationalQ           …
                            0.07  quotient
```

Every file that predates the ℚ development elaborates in under 0.6s.
Each run re-elaborates its imports, so the marginal costs are roughly
rationalQ 36s, rationalInv 21s, rationalAlgInv 11s, rationalEffective
6.5s, intNonZero 1.6s.

Within `rationalQ` the cost is superlinear in file length: 1.2s → 7s
over the first 22 defs, 7s → 23s over the next 40. Items that are
free early (`qcls`, `dInt`) cost 0.05–0.3s each when they appear late.
The heaviest single items are the big explicit `trans`/`cong` chains
and the multi-level `quot-elim`s: `qAddAssoc` +3.8s, `distribNum`
+3.7s, `qDistribL` +2.7s, `crossAssocNum` +1.9s, `crossAddWD` +1.8s,
`qMulWDInner` +1.8s.

## The split

`NOVA_PROFILE=1 nova elab src/nova/rationalQ.nova`, 36.6s wall:

| phase | calls | time | share |
|---|---|---|---|
| engine (`spEqElemC`/`spEqTyC`) | 11,432 | 16.4s | 45% |
| ├ element rewrite fixpoint (`rwNfElemS`) | 78,133 | 8.6s | 24% |
| │ ├ candidate scan | 108,445 | 4.1s | 11% |
| │ └ beta-normalisation | 108,445 | 3.8s | 10% |
| ├ type rewrite fixpoint (`rwNfTyS`) | 56,736 | 2.5s | 7% |
| └ rest (whole-equation match, hops, descent) | | ~5.3s | 14% |
| kernel replay (`kCheckEqElem`/`Ty`) | 10,533 | 5.1s | 14% |
| item check (`kCheckDefItem`) | 269 | 3.6s | 10% |
| candidate-set construction (`mkCandSet`) | 11,432 | 2.3s | 6% |
| unaccounted (elaboration proper, parse, print) | | ~9s | 25% |

Notes:

* Only 1,951 of the 11,432 attempts are element conversions; the rest
  are type conversions.
* Candidate sets average **90** entries per attempt.
* The eager kernel replay is a **gate**, not a search oracle. Stubbing
  it out (to measure its cost by subtraction) makes `rational.nova`
  fail at `intAddScaleZeroL`: without it a rejected certificate reaches
  the item-level check, which fails the item outright. `attemptE` takes
  ONE shot — on replay failure it returns Left and the caller retries
  with a different *refinement*, never with a different candidate. Its
  5.1s cannot simply be deleted.
* `mkCandSet` is rebuilt per attempt from `st.lemmas`, which only
  changes between items — and `rwNfElem` rebuilds it again per call.

## Head-symbol index: measured, no win

`rewriteElemS` is candidate-major (one full descent per candidate, up
to `rwFuel = 40` rounds), and `matchElemP` is purely syntactic and
first-order — the only wildcard is a pattern variable at the head. So
a candidate can only fire if its lhs head symbol heads some subterm of
the target, and filtering on that is exact.

Implemented: `hTagElem` (outermost constructor, signature references
discriminated by name), `tagsElem`/`tagsTy`/`tagsPoly` mirroring
`elemSize`'s traversal, and a `plausible` filter in both rewrite
fixpoints.

Result: **no measurable change** (37.51s vs 37.46s; engine 16.7s vs
16.9s — inside noise). Two reasons, both measured:

1. The filter keeps **46%** of candidates on average. Head symbols are
   not as discriminating here as expected, because the hot terms are
   δ-expanded `ℕ-elim`/`quot-elim` spines that share heads.
2. The scan it shortens is only 4.1s of 36.6s (11%), and the filter's
   own cost — one `tagsElem` walk plus a `SortedSet` build per round,
   135k times — is of the same order as what it saves. Rejecting a
   candidate was already cheap: `matchElemP` fails on the first
   constructor comparison.

Reverted. The lesson is that the scan was never the bottleneck.

## Two fixes, measured

### Cache the Σ-level candidate partition

`mkCandSet` ran, per attempt: a structural `lhs /= rhs` filter over
every lemma, then `ordered` (which computes `elemSize` on both sides
three times and `permutative` once per candidate), then a second
`elemSize`/`permutative` pass for the hop set — and `hypCands`
recomputed `ordered st.lemmas` on top. All of it depends only on the
lemma store, which changes once per accepted equation.

Now computed when a lemma is added and stored in `ElabSt`. The lists
are exactly the old ones: `ordered` splits into shrinking-then-rest
with order-preserving filters, so `ordered (A ++ B) = shrinkA ++
shrinkB ++ restA ++ restB`.

`cands` 2.30s → 1.38s; wall 36.6s → 35.1s. Real but small.

### Memoise definition normal forms — the big one

`betaElem (SigVar x es)` δ-expands the definition and **re-normalises
its whole body, every time the name is mentioned**. At a top-level item
the declaration context is empty, so the spine is empty and the
substitution is the identity: the call is literally "recompute
nf(body) from scratch". The bodies here are things like `qAdd`'s double
`quot-elim`, whose normal forms are enormous — this is the same
δ-expansion that makes obligation printouts unreadable.

A definition's body mentions only earlier entries, and names are
module-qualified, so nf(body) is stable and memoisable on the name.

Σ was **not** append-only at the time: the hole machinery flipped a
`SigDecl` (stuck hole) to a `SigDef` in place, and constraint deletion
rebuilt Σ. A cached normal form could mention a name whose meaning had
just changed, so both tables were dropped at those sites. (Since the
hole-support removal below, Σ only ever extends during a run, the drop
sites are gone with the machinery that needed them, and the caches
live for the run's whole lifetime.)

Result, `rationalQ`: **35.1s → 18.6s**. engine 16.5s → 6.1s (−63%),
`cands` 1.38s → 0.25s (−82%). The kernel's 5.1s and the item check's
3.6s are unchanged — they normalise through their own path.

Corpus, before → after:

```
rationalAlgInv     72.79 → 28.49   2.6x
rationalEffective  68.41 → 27.28   2.5x
intNonZero         61.91 → 26.15   2.4x
rationalInv        60.34 → 23.84   2.5x
rationalQ          37.47 → 18.45   2.0x
eqInt               1.87 →  0.93   2.0x
definingEq          1.13 →  0.08   14x
```

## What the numbers point at next

1. **The kernel's own normaliser.** After the memo, `kernel` (5.1s)
   and `kitem` (3.6s) are together 47% of the remaining 18.6s and did
   not move at all — they normalise through `Nova.Kernel`, not
   `Nova.Elaboration.Beta` (then still named `Nova.Kernel.Beta`). The
   same memo applied there is the obvious next
   step, and it is the trusted path, so it wants the principled version
   (nf stored on the Σ entry) rather than a global IORef.
2. **The remaining engine time**, 6.1s over 11,432 attempts.
3. **The superlinear curve.** Even memoised, cost per item still grows
   with the number of preceding items, because every attempt scans a
   lemma store that only grows. That is the structural issue the
   head-symbol index failed to address.


## Scoping the lemma store — and checking the corpus in one run

`st.lemmas` accumulated across every module of a run, so a module saw
the lemmas of modules it does not import, whichever happened to be
elaborated earlier. That is the root of ProvingFeedback's B-5/B-8, and
it is what made an aggregate root impossible: importing all 36 modules
into one file failed with

```
Error: module intEffective has open obligations and cannot be imported
  [1] (p : ℕ ⨯ ℕ) ⊢ p .π₁ ≐ p .π₂ : ℕ
      at: def intRRefl: checking ⋆ [replay failed: proof argument type mismatch]
```

— `intRRefl` is `⋆` at a goal that is plain `plusComm`, and the module
passes standalone. Some earlier module's lemma matched the shape first
and produced a certificate the kernel rejects; since `attemptE` does not
retry with another candidate, the equation was assumed instead.

Each module's own lemmas are now archived under its name when it
finishes, and entering a module rebuilds the visible store as the
concatenation of its import closure's archives, newest module first.

**For a standalone run this is a no-op**: the loader loads exactly the
root's closure, so every previously elaborated module is already in the
closure and the flattened order is unchanged. The corpus passing
unchanged (142/142, 36/36) is therefore an exact regression test.

What it buys:

* the aggregate works — and in **either** import order, alphabetical or
  topological, which is the point: a module's acceptance no longer
  depends on what else is in the run;
* the whole corpus checks in **26.1s** in one run, against **129s** for
  the per-file sweep and 54.7s for maximal-modules-only;
* `check-elaborations.sh` now runs `src/nova/all.nova` by default (31.5s
  including `pack build`), verifying first that every module is listed;
  `--per-file` keeps the old sweep.

Since a module elaborates inside `all.nova` exactly as it does
standalone, the aggregate *subsumes* the per-file sweep rather than
weakening it.


## The kernel's own normaliser

`Nova.Kernel`'s `kElem`/`kTy` never touch the elaborator's normaliser —
they
have their own copy of the same rules, fuel-bounded inside `KM`, and
the same defect: `kElem sig (SigVar x es)` δ-expands the definition and
re-normalises its whole body on every mention. That is why the
`Beta` memo left `kernel` (5.2s) and `kitem` (3.7s) untouched.

The first cut put both tables in a shared `Nova.Kernel.NfCache`
module, kept separate per normaliser and cleared together at the
then-existing non-monotone Σ sites. (That module was dissolved by the
per-call decision in the next subsection; the clearing sites went with
the hole machinery.) `kElem` also short-circuits when the spine is
empty: the substitution is the identity there, so the cached form IS
the answer and the re-traversal can be skipped entirely.

One consequence worth naming: `burn` is not charged for the contractions
inside a cached body, so a certificate that previously exhausted fuel
may now replay. Fuel is a resource guard, not a soundness mechanism, and
the change only makes the kernel accept more — never a different normal
form.

### …and where that memo is allowed to live

NovaPipeline is explicit: *"Everything above the kernel is UNTRUSTED …
the kernel re-establishes every judgement from its own Σ"*. A normal
form computed by the elaborator is precisely what the kernel may not
believe, so the two normalisers **cannot share a table** — not as a
global, not on the Σ entry, not anywhere the elaborator can write.

So the kernel's memo is state of `KM`, alongside the fuel it already
threads, populated only by `kElem`/`kTy` themselves and living for one
`runKM` call. Nothing crosses the boundary, and the kernel stays
stateless and total from the outside.

The per-call scope costs almost nothing, because the repetition is
*within* a check — a term mentions its dependencies many times over:

```
                    global IORef   KM state (per call)
wall                    7.96s          7.99s
kernel replay           0.51s          0.98s
item check              0.32s          0.29s
```

Against the 5.20s baseline the per-call cache keeps ~80% of the win and
is sound by construction, which is the better trade.

**The trusted path now contains no `unsafePerformIO`.** What remains is
in the elaborator's normaliser, which `Nova.Elaboration` alone imports.
It was called `Nova.Kernel.Beta` at the time — a name that invited
exactly the wrong assumption — and was renamed `Nova.Elaboration.Beta`,
with the memo tables folded back into it. (An unrelated arrival
briefly reused the old name: the dormant derivation artifact's
kernel-side walker family, which really is kernel-layer and now lives
at `Nova.Kernel.Dormant.Beta` with the rest of that artifact — see
docs/NovaDerivations.txt. The two coexist by design.) That memo is below the trust boundary: a stale entry there can only
cost completeness (a bad certificate is rejected at replay), never
soundness. Moving it into `ElabSt` would mean threading a cache through
`betaElem`'s 100 internal recursions and 64 call sites, or making `Sig`
a record; worth doing if the goal is zero `unsafePerformIO` anywhere,
but it buys correctness of nothing that is currently wrong.

`rationalQ`, on the same base:

```
                 before    after
wall             17.65s    7.96s
kernel replay      5.20s   0.51s   -90%
item check         3.68s   0.32s   -91%
engine             3.96s   3.97s   unchanged
```

Corpus:

```
rationalAlgInv     28.49 → 12.15
rationalEffective  27.28 → 11.74
intNonZero         26.15 → 11.13
rationalInv        23.84 → 10.54
rationalQ          18.45 →  7.51
all.nova (one run) 26.10 → 14.93
```

`./check-elaborations.sh` is now **19.5s** including `pack build`
(which is itself 15.6s of it — the corpus check proper is under 5s,
against 129s when this started).

A measurement caveat recorded here because it nearly caused a
misattribution: the engine figure of 6.1s quoted in the previous
section was taken before the branch was rebased onto the updated
`proving-in-nova`, whose `integer.nova` moves `zeroEq` earlier. That
changes where an equation-typed lemma enters the store and is worth
~2s on its own. Re-measuring the previous commit on the current base
gives 3.96s, so the kernel memo left the engine untouched, as it
should have.

## The Σ-lookup index

A Chez source-profile (per-expression execution counts, mapped back to
Idris definitions — the driver is three lines, trivially recreated:
`compile-profile 'source` + `load-program` + `profile-dump-list`) put `sigLookup` and its per-entry costs at ~40% of
ALL execution: a linear scan of the Σ snoclist comparing
`Maybe String`, run on every SigVar occurrence of every normalization
walk. Substitution — the natural suspect — measured ~4%.

Fix, two halves along the trust boundary: the kernel gets a per-call
name→entry `SortedMap` in KM state (Σ is fixed for one runKM, so a
positive hit is stable — same discipline as its nf memo); the
elaborator gets a global positive-only cache beside the nf memos —
cleared, at the time, at the same sites as those memos; today none of
them is ever cleared (Σ only extends) — negatives never cached.

Found on the way, confirmed by exploit: the Chez backend DEDUPLICATES
syntactically identical nullary CAFs, so `betaElemNf`, `betaTyNf` and
the new table — all `unsafePerformIO (newIORef empty)` — silently
shared ONE ref. The first two had always collided harmlessly (term-
and type-def names are disjoint); the new table shared keys with both,
and a SigEntry reinterpreted as an Elem normal form walked into
`substVar` as garbage. All tables are now allocated in a single IO
action, distinct by construction.

all.nova, scoped default: wall 11.0s → 9.3s; elaborate phase 10.3s →
8.6s; kernel replay 0.83s → 0.44s; item check 0.51s → 0.26s; engine
0.38s → 0.17s. The profile's top family is now the rewrite matcher
(matchElemP + rewriteElemS + descent ≈ 21%) — Part II's target.

## The cost of a hole

Per-item timing (the `item <name>` label) put the four heaviest proof
items at 100–583ms; their explicit calc-chain twins run 6–26× faster
(SearchlessElaboration §15). A controlled three-way variant of the
heaviest — same lemma, same imports, one run — decomposes the cost:

```
swapA  combinator spine, blanked `_` indices     458ms
swapB  the IDENTICAL spine, indices spelled       10ms
swapC  the calc-chain twin                        10ms
```

The trans/cong spine was never the problem — fully spelled it costs
the same as a chain. **~98% of the original's cost is the holes**, and
the mechanism decomposes into four parts:

1. **The attempt tax.** The solver is only reachable after a FULL
   FAILED discharge attempt (ProvingFeedback E-1 documents the
   ordering and why it also loses solutions). Every hole-bearing
   equation pays: a complete engine walk with the hole stuck —
   guaranteed to fail — then the solve, then a complete re-attempt
   with eager kernel replay. ~16 holes in swapA ≈ 2–3× on every
   conversion, on the most expensive operands in the corpus.
2. **Cache demolition on every flip.** A solved hole flips its Σ
   declaration to a definition IN PLACE — non-monotone — so
   the cache reset wiped the def-nf memo and the Σ-index; the next
   conversion re-normalised every mentioned definition from scratch.
   A (then-added, since removed with the machinery) `nf-reset` counter
   measured 1,145 wipes discarding ~10.9k cached normal forms in one
   small run. Holes couple directly to the SIZE
   factor: cost ≈ #holes × rebuild-all-nfs-in-scope.
3. **Tier starvation.** An unsolved hole side is a stuck `_r…`
   reference — never α-identical, never computationally joinable — so
   the ↓ loop's free tiers (steps 0 and ½) cannot fire at sites that
   are free in the spelled variant.
4. **Kernel work per solve.** kCheckSolution against the Σ prefix per
   attempt (plus legalize's δ-walk retries), item-end re-mirroring of
   each solved hole, and — for late solves — the whole-item internal
   RERUN (the `calls=2` items pay everything twice).

Remedies as assessed then, in leverage order: solve BEFORE the doomed
attempt when a side is syntactically an unsolved-hole spine (E-1's
candidate fix 1 — it repairs the completeness gap and deletes
mechanism 1 in the same move); dependency-scoped cache eviction on
flip instead of wipe-all; batching flips per item to avoid rerun
churn. (Overtaken: hole support was removed outright — next section —
so this list survives as REQUIREMENTS on the metavariable redesign,
alongside ProvingFeedback E-1/E-1½.) And a corpus-level
decision: the index-blanking sweep trades ~45× elaboration time on
heavy items for written terseness — under the AI-operator metric
(generation is cheap; latency and feedback are not) that trade runs
the wrong way.

## The hole-free corpus

Every `_` in the corpus is now spelled: the four explicit twins replace
their [style:rw] originals under the original names; the a92a9f7
blanking is reverse-applied from git where its hunks still fit; the
remaining 877 holes were filled by the elaborator itself — a DEBLANK
emitter (deblankLines in Nova.Elaboration, on the NOVA_AUDIT stream)
printed every solved hole's inferred solution with its source span, and
tools/deblank.py spliced them back over the `_` tokens, refolding
δ-normal +/* renderings into operator form. (Emitter and splicer were
one-shot scaffolding and are removed with hole support — git history
keeps both; tools/tidy-surface.py later normalized the paste
artifacts.) Six sites needed hand
repair (inlined definition bodies rendered motive-less: Rat's code,
nzToInt/qOfNzq spines, one ∈-precedence paren). The census closes at
ZERO minted holes across the whole corpus; per-file sweep, both
all.nova modes and 150/150 tests green.

The timing collapse exceeded the per-item prediction:

```
                     holes (before)   hole-free
wall (all.nova)          9.3s           1.44s
elaborate phase          8.6s           0.60s
load+parse               0.65s          0.79s   (now the largest phase)
engine attempts          6,457          1,074
eager kernel replays     4,016          1,074
kernel replay time       0.44s          0.12s
item admission           0.26s          0.19s
solve calls              1,455          33
```

Session arc on the same corpus content: 33.6s → 9.3s → 1.44s. The
hole machinery was not one cost among several — with the search
already scoped, it WAS the elaboration cost: five of every six engine
attempts existed to fail around a stuck hole. This is the baseline the
hole-support removal (and the later redesign) starts from.

## Where it stands

Hole support was subsequently removed outright (elaborator, kernel,
specs), which shaved a further ~10% off the elaborate phase and made
every cache in this file's story permanent for a run: Σ only extends.
The corpus has since grown by the algebra/order/reals modules and
checks in ~2.2s end to end, with the trusted side (kernel replay +
item admission) and load+parse as the dominant phases and the
discharge engine at ~1% of wall. The open performance items are the
ones the growth curve will surface: load+parse scales with the corpus,
and the metavariable redesign must not reintroduce mechanisms 1–4 of
"The cost of a hole" above.

## The ℝ regression: substitution towers

The completeness/abs/metric development blew the corpus up from ~2.2s
to **6:07 wall** (elaborate phase 384s under NOVA_PROFILE). Two items
were 80% of it: `realComplete.realLimClose` **230s** and
`realAbs.realAbsAbs` **74s**. Phase split: item admission (`kitem`)
153s, eager kernel replay 105s, engine 82s (of which `rwNfTyS` 63s at
~27ms/call).

A Chez source profile (the §"Σ-lookup index" driver; entries are flat
lists `(count path bfp efp line col)` — count first) put the
substitution family at **55% of all execution**: `substVar` 26.9%,
`substElem` 22.9%, `under` 5.1% — against ~4% when last measured. The
matcher family (`rewriteElemS`/`matchElemP`/descent) was 17%, the
kernel normaliser + KM plumbing ~10%.

The mechanism: `under σ = Ext (Chain σ Wk) ☐₀`, and
`substVar n (Chain s t) = substElem (substVar n s) t` — so resolving a
variable through an `under`-tower of depth k costs **k full copies of
the resolved payload**, one per tower layer (x[σ][↑][↑]… applied
literally). liftK/under towers are everywhere: every binder crossing
in every β-contraction of every normaliser walk. The ℝ corpus made the
payloads big and the towers deep: `realAbsAbs`'s eight type-level
attempts each δ-expand ~2.9k-node written types to **~137k-node**
normal forms (measured via a temporary `sz-att-ty-nf` bump); its
structural twin `realAbsNeg`, whose expansions stay small, costs 2.3s
against 78s.

### Fix: shift-accumulating substVar (+ two shortcuts)

`substVar` now resolves with a pending-shift accumulator: weakening
compositions coalesce (`go n (Chain s Wk) k = go n s (S k)`) and the
shift applies as ONE pass at the resolved payload (`t[↑ᵏ]` via a
`wkTower` whose resolution allocates nothing). Extensionally identical
to the literal equations. Alongside: `substElem`/`substTy` return the
term unchanged at `Id` (terms are pure trees — nothing pending), and
the elaborator's `betaElem`/`betaTy` got the kernel's empty-spine
shortcut (the cached def-nf IS the answer; previously each top-level
mention paid a full copy through `Terminal` plus a full re-walk).

Result: corpus elaborate **384s → 235s** (wall 6:07 → 3:29), 138/138
tests green. `realLimClose` 230→113s, `realAbsAbs` 74→46s; probeB
(realAbs standalone) 95→61s with engine 33.5→16.2s, kitem 28.7→19.8s,
kernel 24.7→16.9s. Post-fix source profile: subst family 31% (the
accumulator's `go` is now the top single function at 15.5%), matcher
29%, kernel+KM 16%.

### What the numbers point at next (measured, not guessed)

Isolating `realLimClose` (truncated-module diff): its 110s decomposes
into ONE `kitem` call of **51s**, 14 attempt-level kernel replays of
~2.3s each, and 14 type attempts whose `rwNfTyS` costs ~1.26s/call —
but its conversion types δ-expand to only ~4k nodes. The regimes
differ: `realAbsAbs` is size-bound (137k-node types), `realLimClose`
is walk-bound (candidate-major matcher rounds; many replays per item).

Kernel-side instrumentation of the replay split, one probeE run:
`krepl-ty-nf` (normalising the two sides) **49.4s over 6,366 replays**
vs `krepl-ty-steps` (replaying the recorded steps) **0.14s**; elements
add 14.7s vs 3.4s. Average steps per certificate: **0.23**. Three
ceilings measured on the way, all ~zero:

* a cross-runKM def-nf cache (global-IORef prototype): 226→216s — the
  per-call memo already catches what matters, re-confirming the
  "…where that memo is allowed to live" measurement on the new corpus;
* a whole-term side-nf memo: **0 hits in 14,668 lookups** — replayed
  sides never repeat syntactically;
* tier-1 replay cost (`kernel-t1-*`): 0.4–2.3s — comp-joinable
  equations replay cheaply already.

So the dominant remaining cost is: **thousands of near-miss conversion
checks decided by brute-force normalise-both-and-compare**, in the
kernel (stepless-FBeta replays, head-exposure `kTy` calls in
`kCheckE`/`kInferE` — the Π-tower is re-normalised at every spine
node) and in the engine (rwNf of both sides before any lemma is even
needed). The sides are mostly-shared trees differing along one spine,
and ~85% of tier-2 certificates end stepless — provable by plain δβ
with no lemma machinery at all.

Ranked plan:

1. **Diff-directed conversion ("join check")**: recursive compare with
   syntactic-equality pruning at every node, whnf + head-match on
   mismatch — decides exactly nf-equality (untyped, η-free, as today)
   while touching only the differing spine. Three deployment sites:
   the kernel's stepless-FBeta replay path, the kernel's head-exposure
   sites (whnf instead of full kTy at `case ty' of` matches), and an
   engine tier 1½ before candidate assembly. Measured ceiling ~60s of
   probeE's 206s in the kernel alone, plus most of the engine's rwNf.
2. **Matcher round structure**: after a successful rewrite, only the
   rewritten path can expose new redexes — re-normalise along it
   instead of `betaElem` on the whole term per round; keep sizes with
   the `seen` entries to make the cycle check O(1) on mismatch.
3. The structural end-game if 1–2 are not enough: sharing-preserving
   normalisation (NbE/closures) — the per-occurrence payload copy that
   substitution still pays is inherent to tree substitution.

(Overtaken before implementation: the αβ-conversion survey below made
plan 1 moot for the elaborator — the strict subset removes the work
instead of optimising it — and re-scopes its kernel half as the
replay-side redesign of the new architecture.)

## The αβ-conversion survey (NOVA_STRICT_CONV=1)

A design decision, then its measurement. The decided architecture:
automated conversion is **α + the computation rules + Prf-irrelevance
(𝟙/𝟘/Prf) + named whole-equation matching** — no δ on equation sides,
no η, no hops, no positional rewriting. Head exposure of TYPES keeps
δ, but per-item whitelisted (a `using`-style unfold clause); everything
outside the subset is the operator's to discharge, later assisted by
explicit tactics / terser transport syntax. Rationale: performance
must be consistent and proportional to what is written — the 34×
realAbsNeg/realAbsAbs cliff is invisible in source and inherent to
δ-driven conversion; terse proofs can be recovered intensionally
opt-in, not as the default cost model.

The survey mode implements the elaborator side of exactly that subset
(kernel unchanged — it only ever accepts more than the engine emits):
`rwNf*` gated to the computational normaliser, η/hops/`spCongC`
disabled, equation sides never δ-expanded, and every CHECKING-position
head exposure routed through a logged whnf-δ (`exposeE`/`exposeT`,
`unf <module>|<name>` labels — the whitelist survey). Failures
surface as ordinary obligations; a hard mid-checking failure drops the
module and cascades. Dedup keys carry a size prefix (cheap prefilter).

Corpus results, one run, 24s wall (default mode untouched: 138/138,
209s):

* **1,031 obligations across 497 of ~1,100 items** (2.1 per affected
  item). By site: 676 inferred-vs-expected type conversions, 310
  ⋆-proofs, 32 quot-elim well-definedness, 9 chain steps. 57 carry a
  `hint:` naming an existing store lemma — pure `using`-clause
  additions; the bulk of the rest are defining-equation shapes
  (`plus Z n ≐ n`), the auto-generatable `<def>.eq` lemma family.
  Heaviest modules: rationalQ 133, rationalOrder 61, realLattice 56,
  realOrder/rational 44, realAdd/intAbs 39.
* **Whitelists are small and stable**: 426 (module, name) unfold pairs
  over 60 modules — ~7 per module, ≤22 at the worst (realComplete);
  the names are exactly the type abbreviations (Int, Q, Id, LeN, LeZ,
  Sign, LeQ, Real, RSeq, Regular…). Obligation statements stay in
  surface vocabulary.
* **4 modules dropped**, all genuinely dependent on removed
  automation: stream (+ streamEq/streamBisim by cascade) — coinductive
  props exposed only by HYPOTHESIS rewriting under squash-elim — and
  vectByIndAppend (ℕ-elim-computed type family exposed by
  hypothesis rewriting). These need restatement or an explicit
  exposure construct.
* **The cost model collapses as predicted**: engine 49ms, candidate
  assembly 78ms, tier-1 4ms — the discharge engine is now noise. Of
  the 24s: ~15.2s is the UNCHANGED kernel's δβ normalize-and-compare
  replaying the certificates that still succeed, ~2s load+parse, the
  rest obligation bookkeeping/display. With the kernel ported to the
  same subset (αβ compare + whitelisted exposure + named-lemma
  instantiation — a simplification, not an optimisation: the step
  language largely disappears), the corpus projects to **~5s,
  parse-dominated**, from 367s at this file's start.

Migration is the remaining cost and it is mapped, mechanical, and
hint-assisted: add the named `using` clauses the hints already print,
generate the defining-equation lemmas, spell the cong/trans chains the
310 ⋆-sites need, whitelist ~7 unfolds per module, restructure the 4
dropped modules.

## `<def>.eq` citations and the mechanical sweep

The defining-equation lemma family landed as a NAMESPACE, not as
minted items: a using-clause name `<def>.eq` resolves against Σ
(aliases, then raw, then progressively stripped qualifiers — the same
clause must parse in a standalone root and in the aggregate) and
licenses UNFOLDING that definition in the site's equation joins. The
strict join is then `comp ∘ unfold[cited]` — α + computation + exactly
the cited δ — and the certificate stays the stepless FBeta the
unchanged kernel already replays. No Σ entries, no new certificate
forms, no cost for items that cite nothing. The engine's syntactic
congruence descent (spCongC, strict children) stays enabled: it is the
certificate-assembly twin of the faithful decompose splitting — one
deterministic pass over the sides' common structure — not the banned
positional candidate search. Obligations that would close under
citations they don't yet have get a second hint stream: the sides'
mentioned definitions are joined iteratively and reported as
`closes by citing x.eq, …`.

The clausal-def macro now cites for its own output: clause lemmas
carry `using (<f>.eq)` (their ⋆-bodies hold by f's computation), the
uniqueness lemma carries the clause lemmas plus `<f>.eq`. Constructed
SItems take operator names fine — the surface parser, which cannot
yet spell `+.eq` in a using list, is bypassed.

The sweep (scratchpad `strict-sweep.py`) parses the survey report —
attributing each obligation to its item by the `at: def` site, cursored
through module order — and merges both hint streams into the items'
using clauses, iterating to fixpoint. Two rounds converge:

```
obligations   1,018 → 240   (76% closed mechanically)
items edited  386 across 58 corpus files (+489 lines of using clauses)
dropped       stream/streamEq/streamBisim/vectByIndAppend (unchanged)
```

Default mode is untouched throughout: 138/138, all.nova Accepted
(3:17 — the added clauses only widen item scopes, which the one-shot
attempt tolerated everywhere).

The 240 residue decomposes into: ~35 sites blocked ONLY by operator
names in surface using-lists (`nat.+.eq` — a parser affordance away);
the eta/uniqueness ⋆-cases and induction step-cases that genuinely
need trans/cong chains (hypothesis on one side, store lemma on the
other — hop territory, i.e. the operator's or a future tactic's job);
and the 4 hypothesis-rewriting modules.

The post-sweep strict profile is the kernel-port motivation in one
line: **engine 0.6s, kernel replay 55s** (1,406 certs, wall 62s) — the
unported kernel re-deciding by full δβ normalize-and-compare exactly
the equations the strict engine joins in milliseconds. (kitem is ~0
only because a dirty run skips item admission; a zero-obligation
migrated corpus re-adds it — also αβ-cheap once the kernel speaks the
subset.) The port — αβ compare + whitelisted exposure + named-lemma
instantiation replacing the step-replay language — remains the single
remaining performance item.

## The kernel port: the tiered replay

The kernel now speaks the strict subset, with the historical path as
a fallback rather than the default. Three pieces:

* **ECert carries its licenses** (`unfolds : List String`) — the
  site's cited `<def>.eq` names, stamped by the elaborator at the
  attempt boundary. Operator-provenance data, like the body: the
  kernel never validates the list, because soundness never depends on
  it — everything the licensed join equates is δβ-equal — it only
  bounds the fast tier's work to what the source names.
* **The join normalizer** (`kJoinElem`/`kJoinTy`, kernel-owned, in
  KM, one fuel per contraction): every computation rule plus
  unfolding of exactly the licensed term definitions; TYPE heads
  expose freely (ty-x-β, and El-decoding through a weak-head δ of the
  code) — the head-exposure discipline, pending per-item type
  whitelists as surface syntax. Alongside it, `kWhnfE`/`kWhnfT`:
  fueled weak-head normalization with δ, for head matches.
* **Tiered replay**: `kEqElem`/`kEqTy` run the whole replay under the
  join policy first (licenses = the certificate's, unioned with the
  parent's down final-recursions) and rerun under full δβ from the
  saved fuel state on any failure. Acceptance only ever grows, so
  every pre-strict certificate — and all of default mode — keeps
  working unchanged; a fully migrated corpus lets the fallback (and
  the δβ side-normalization it keeps alive) be deleted. Item
  admission's head exposures (`kCheckE`/`kInferE`'s `case (kTy ty)
  of` matches) switched to weak-head normalization — one site stayed
  full (el-qiit-intro compares the carried signature structurally,
  caught by elab-data tests).

Measured, same corpus, 138/138 both modes:

```
strict all.nova     62s → 16.5s   (kernel replay 55s → 11.3s;
                                   realLimClose 230s → 113s → 3.8s
                                   across the session)
default all.nova    3:17 → 1:39   (whnf exposure + tier-1 catching
                                   comp-joinable replays)
```

What remains of the 11.3s: stepped certificates (whole-equation lemma
steps verify through `stepElem`, whose lemma-statement normalization
is still full δβ) and joins whose engine/kernel vocabularies diverge
at corners — both bounded, both shrink as the migration replaces
δβ-dependent certificates outright. End state on a fully migrated
corpus: delete the KFull tier, `stepElem`'s δβ internals, and the
per-call def-nf memo that exists to serve them.

## Closing the tier: per-component rescues, operator citations

Instrumenting the fallback rate (temporary khit/kfall counters,
reverted) localized the residual kernel time precisely: type replays
hit the join tier at 99.4%, while HALF the element replays fell back
— 331 of 342 were stepped certificates failing the step machinery's
SYNTACTIC checks (position type vs lemma type, subterm vs lemma lhs
instance, and then the final compare) on pairs that are δβ-equal but
join-unequal: a lemma statement or type index mentions a definition
outside the cited set. The whole-replay fallback then re-ran full δβ
from scratch.

Fix: the step machinery went policy-aware (`licensed`/`goE`/`goTy`/
`stepElem`/`stepTy` normalize under the replay's tier; shape
exposures by weak-head normalization), and its three equality checks
try join-syntactic first with a PER-COMPONENT δβ conversion rescue on
mismatch — localized to the offending pair instead of failing the
tier. Under KFull the inputs are already δβ-normal, so the rescue is
an identity check and historic behavior is unchanged. Result:
fallbacks 342 → 3, strict corpus 16.5s → 12.4s (kernel replay 11.3s
→ ~7.5s — now mostly the rescues themselves and the survey's hint
machinery, both of which vanish with the migration), and three more
edge certificates accepted (acceptance is monotone). The unfold-hint
name pool also moved off rendered-string scanning onto a syntactic
collector (`refsE`/`refsT`).

Using-list names then became general dotted paths whose segments are
identifiers OR operator tokens (`nat.+.eq` parses; `.` is not in the
operator alphabet, so the tokens separate cleanly), unblocking the
operator-named defining-equation citations. One more sweep round:
**235 → 169 obligations, with ZERO hints remaining** — every
mechanically-closable site is closed. The residue (113 ⋆-goals, 22
conversions/chain steps; rationalQ 27, integerMul 18, rationalOrder/
nat 14 each) is genuine trans/cong chain-writing — the operator's or
a future tactic's job — plus the four hypothesis-rewriting modules.

Where the corpus stands, end of campaign, 138/138 both modes:

```
                    session start   now
default all.nova        6:07        1:24
strict  all.nova          —         12.4s  (169 obligations to migrate)
realLimClose (item)     230s        ~4s
```
