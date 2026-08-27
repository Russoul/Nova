# Coinductive types
%stub

`ν` at a one-hole polynomial: streams, conaturals, and proofs by
coinduction.

## Polynomials

- `F ::= 𝕏 | K t | F ⨯ F | F ⊎ F | (x : t) ⨯ F | (x : t) → F`; external
  pieces are codes, and `𝕏` is the hole.
- `ν (K a ⨯ 𝕏)` is streams of `a`; `ν (𝟙 ⊎ 𝕏)` is the conaturals.

## Observation and corecursion

- `out t` observes one step and **infers**.
- `corec (x : a. f) u` — carrier code, coalgebra body, seed;
  checking-only, since the polynomial comes from the expected type.
- β: `out (corec …)` runs one step, which is what makes the observation
  lemmas close by computation.

## Coinduction

- `coind (x y. R) p (x y h. q)` at `l ≡ r ∈ ν F`: an Ω-valued
  invariant `R`, a proof `p : R l r` that it holds of the endpoints,
  and the one-step closure.
- Idioms: squashed Σ invariants unpacked with `squash-elim`;
  `u ≡ ⟨machine⟩` components acting as unfold-once rewrite rules.

## Bisimilarity

- Observational equality in `Ω`, bisimilarity as the impredicative
  greatest fixed point, and `bisimReflect`.
