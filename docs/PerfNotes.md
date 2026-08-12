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
   `Nova.Kernel.Beta`. The same memo applied there is the obvious next
   step, and it is the trusted path, so it wants the principled version
   (nf stored on the Σ entry) rather than a global IORef.
2. **The remaining engine time**, 6.1s over 11,432 attempts.
3. **The superlinear curve.** Even memoised, cost per item still grows
   with the number of preceding items, because every attempt scans a
   lemma store that only grows. That is the structural issue the
   head-symbol index failed to address.
