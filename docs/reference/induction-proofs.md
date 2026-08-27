# Proving by induction
%stub

When computation is not enough, the eliminator is the proof.

## An equality motive

- The same `ℕ-elim` you use to compute; the motive is now an equation.
- Parenthesise it: `(k. Z + k ≡ k)`.

## Why each case is usually `⋆`

- In the step case the induction hypothesis is an equation in scope, so
  reflection applies it silently.

## A worked proof, start to finish

- `zeroPlusId`, then something that needs it.

## Choosing what to induct on

- `+` recurses on its **second** argument, so `n + Z ≡ n` is free and
  `Z + n ≡ n` needs induction. Picking the reducing order.

## Over your own types

- The sort's eliminator; the prop-valued `<Sort>ElimP` for equational
  goals ([Quotient inductive-inductive types](#qiits)).

## Generalising

- A lemma stated at the shape you need discharges every instance
  ([The discharge engine](#discharge)).
