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
* The eager kernel replay is **load-bearing for search**, not just
  verification. Stubbing it out (to measure its cost by subtraction)
  makes `rational.nova` fail at `intAddScaleZeroL`: the engine relies
  on replay *failure* to reject a route and try another, so a bad
  certificate that used to be caught mid-search now flows through to
  the item check. Its 5.1s cannot simply be deleted.
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

## What the numbers point at instead

1. **Normal-form caching.** Beta-normalisation is 3.8s inside the
   element rewrite fixpoint alone, and the same δ-expansion is redone
   by the engine's other phases, by the kernel replay, and by the item
   check. A shared normal-form cache (hash-consing, or memoising
   `betaElem` per signature generation) attacks all four at once.
2. **Hoist `mkCandSet`.** 2.3s in `attemptE`/`attemptT`, plus every
   `rwNfElem` call rebuilding it. The Σ-level part is invariant between
   items; only `hypCands` depends on Γ.
3. **Kernel replay, 5.1s over 10.5k calls.** Cannot be removed (see
   above), but is likely dominated by the same normalisation.
