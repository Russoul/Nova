# The library
%stub

A tour of `src/nova`, in dependency order.

## Prelude and basics

- `prelude` (`id`, `∘`, `const`, `funext`), `equality`, `prop`,
  `propCode`, `bracket`, `uip`.

## Data

- `sum`, `id`, `quotient`, `quottyuniv`, `qiitNat`, `qiitBag`,
  `qiitQuot`, `qiitVec`, `qiitInt`, `qiitConTy`, `qiitCross`,
  `vectByInd` / `vectByIndAppend` (vectors by recursion, and append
  proved associative with no cast — [Types without coherence](#coherence)).

## Algebra

- `monoid`, `group`, `groupTheory`, `subgroup`, `quotGroup`, `groupHom`,
  `groupIso`, `ring`, `ringTheory`, `ideal`, `quotRing`, `field`.

## The number tower

- `nat` → `natMore` / `natOrder` / `natDiv` / `natSqrt`
- `integer*` → `intOrder` / `intAbs` / `intQuot`
- `rational*` → `ratBound` / `ratAbs` / `ratLt` / `ratHalf` / `ratArch`
- `real*` — Bishop's regular sequences, `realSeq` and the lessons it
  taught.

## Coinduction

- `stream`, `conat`, `streamEq`, `streamBisim`.

## Reading the sources online

- The [rendered corpus](nova/index.html), syntax-highlighted through the
  LSP's own token classification.
