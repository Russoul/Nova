# Your first proofs
%stub

The three moves that close almost every goal: computation, hypotheses,
and induction.

## Proof by computation

- `⋆` proves any equation whose sides already compute to the same term.
- Why `plusZeroId` is `λn. ⋆` while `zeroPlusId` needs induction — which
  argument the definition recurses on decides.

## Proof by hypothesis

- Reflection: a hypothesis of equation type makes its sides
  interchangeable, so `sym`, `trans` and `cong` are `⋆`.

## Proof by induction

- `ℕ-elim` with an equality motive; parenthesising the motive.
- Where the induction hypothesis comes from and why `⋆` usually closes
  the step case.

## Chaining equations

- A first `≡⟨ ⟩` calc chain, and when to reach for `trans` instead.

## When it does not go through

- Reading the obligation, restating it as a lemma, placing the lemma
  above the failing item.
