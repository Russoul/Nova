# Propositions
%stub

A proposition is a type whose inhabitants carry no information — only
the fact that there is one. `Ω` is where they live, and this chapter is
what changes when a type is one.

## `Ω`, and propositions as types

- A proposition is proof-irrelevant: any two proofs are judgementally
  equal (`el-prf-prop`).
- A proposition **is** its type of proofs (`prop-lift`): `p : Ω` stands
  directly where a type goes, and there is nothing to decode.
- Type equality on the prop cluster is mere equivalence: mutually
  implied propositions are equal (`code-prop-eq`).

## Squashing

- `∥T∥` squashes any type into a proposition; squashing a proposition
  again changes nothing.
- `⋆` auto-synthesises only for **evident** propositions — a squashed
  `𝟙`, or an equation whose sides are already equal.
- `⋆ e` supplies a witness explicitly, for any shape.

## Eliminating a proof

- `squash-elim e (x. body)` eliminates into a **further proposition**,
  and that is as far as elimination goes.
- The workaround when you need data: `⊥` proves a false equation, and
  reflection turns that into a type equality you can cross.

## Propositional extensionality

- Mutually implied propositions are equal codes; `⋆ (f , g)` supplies
  the two implications.

## The connectives

- `⊤ ⊥ ∧ ∨ ⊃ ¬ ↔` are impredicative encodings in `prop.nova`, not
  primitives — including `∨`, since Nova has no primitive sum in `Ω`.
