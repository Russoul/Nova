# Elaborator performance — measurements

Running notes for the `research-performance` branch. Numbers are wall
clock on the branch tip, macOS/arm64, Chez backend, `pack build` at
15.6s for reference.

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

Σ is **not** append-only, though: `flipDecl` replaces a `SigDecl`
(stuck hole) with a `SigDef`, and constraint deletion rebuilds Σ. A
cached normal form may mention a name whose meaning just changed, so
both tables are dropped at those five sites. Flips are rare — once per
solved hole — so this costs nothing measurable.

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

Both tables now live in `Nova.Kernel.NfCache`, shared by the two
normalisers but kept separate per normaliser, and cleared together at
the non-monotone Σ sites. `kElem` also short-circuits when the spine is
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
It used to be called `Nova.Kernel.Beta` — a name that invited exactly
the wrong assumption, and it is now `Nova.Elaboration.Beta`, with the
memo tables folded back into it. That memo is below the trust boundary: a stale entry there can only
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
Idris definitions — the driver lives in the session scratchpad and is
trivially recreated: `compile-profile 'source` + `load-program` +
`profile-dump-list`) put `sigLookup` and its per-entry costs at ~40% of
ALL execution: a linear scan of the Σ snoclist comparing
`Maybe String`, run on every SigVar occurrence of every normalization
walk. Substitution — the natural suspect — measured ~4%.

Fix, two halves along the trust boundary: the kernel gets a per-call
name→entry `SortedMap` in KM state (Σ is fixed for one runKM, so a
positive hit is stable — same discipline as its nf memo); the
elaborator gets a global positive-only cache beside the nf memos,
cleared at the same resetNfCaches sites, negatives never cached.

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
