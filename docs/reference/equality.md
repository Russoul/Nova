# Equality
%revise

Equality in Nova is a **proposition**, and a proved equation becomes a
**judgemental** one. Those two sentences explain most of what looks
strange in a Nova file and most of what makes it short.

## The proposition, standing as a type

`a ≡ b ∈ A` is an element of `Ω`: a mere proposition, formed at
arbitrary `a b : A` (`code-eq`). It is not a type former, and it is not
an inductive family with a constructor.

And yet you write it exactly where a type goes. That is
**prop-cumulativity**: a proposition *is* its type of proofs
(`prop-lift`), so an equality prop stands in a signature exactly as it
stands anywhere else (`e-ty-eq`). There is one spelling, and it is the
proposition itself.

The `∈ A` slot may be dropped whenever the type is determined by the
sides, which in a lemma statement it usually is:

```nova-sketch
def plusZeroId : (n : ℕ) → n + Z ≡ n ∈ ℕ using (nat.+.eq) ≔ λn. ⋆
def plusZeroId : (n : ℕ) → n + Z ≡ n using (nat.+.eq) ≔ λn. ⋆
```

Spell `∈ A` out when the sides are ambiguous, when the two sides have
*different* apparent types and you mean to fix one (`appCong` in
`equality.nova` ends `∈ B a1` for exactly that reason), or when you
find it clearer. The report always prints it.

> There is no longer any difference between writing an equation in a
> **type** position and in an **element** position — a quotient
> relation, an argument at `Ω`. It is the same proposition either way,
> and that uniformity is what retiring the wrapper bought. Quotient
> relations are Ω-valued, which is why
> `ℕ × ℕ / (p q. p .π₁ + q .π₂ ≡ p .π₂ + q .π₁ ∈ ℕ)` needs no squash.

## `⋆` is the proof

Propositions are proof-irrelevant (`el-prf-prop`): any two proofs of the
same proposition are judgementally equal. The canonical form is `⋆`,
for every proposition without exception.

`Refl` is not merely omitted, it is **retired**, and that is forced
rather than stylistic: propositional extensionality moves proofs
between logically equivalent propositions unchanged, and a true equation
is equal at `Ω` to `∥𝟙∥`, so every inhabited proposition must have
literally the same canonical inhabitant.

Consequences worth internalising early:

- You never pattern-match on an equality proof, because there is
  nothing to match.
- Two proofs of the same equation are interchangeable — `equality.nova`
  proves `irr : {A : 𝕌} {v u : A} (p : v ≡ u) → p ≡ (⋆)`, which is UIP,
  as a one-line `⋆`.
- Writing `⋆` at an equation is a *request*: it asks the checker to
  derive that the sides are equal. If it can, the proof is done; if it
  cannot, you get an obligation. [The discharge engine](#discharge) is what happens in between.

## Reflection

The rule that does the work is `el-reflect`: from `s : (a ≡ b ∈ A)`
conclude `a ≐ b : A`. A proved equation is a judgemental equation.

Operationally, every equality-typed **hypothesis** in the ambient
context is reflected and made available to conversion automatically —
hypotheses are always in scope, unlike lemmas, which must be named
([`using`: licences and scope](#using-clauses)). So a proof that merely needs to use its hypothesis is
`⋆`:

```nova
def sym : {A : 𝕌} (a b : A) → (a ≡ b) → b ≡ a ≔ λA. λa. λb. λh. ⋆

def coe : {A B : 𝕌} → (A ≡ B) → A → B ≔ λA. λB. λh. λa. a

def transport : {A : 𝕌} (P : A → 𝕌) {a b : A} → (a ≡ b) → P a → P b ≔ λA. λP. λa. λb. λh. λp. p
```

`coe` and `transport` are the identity function: with `A ≐ B` reflected,
there is nothing to convert. `transport`'s signature still does real
work — it *retypes* — which makes it the standard way to move a term to
a type the kernel would otherwise refuse to convert to.

Two refinements you will meet in practice:

- **Under binders.** A Π-wrapped equation hypothesis can be
  instantiated at a fresh variable, so two neutral functions are joined
  pointwise. That is function extensionality, and `prelude.funext` is a
  single `⋆`.
- **Component decomposition.** An equation between same-headed universe
  codes also contributes its components, licensed by code injectivity:
  a hypothesis `h : (a → 𝟙) ≡ (b → 𝟙) ∈ 𝕌` silently yields `a ≐ b : 𝕌`.
  `class` is **not** decomposed — quotients are deliberately not
  injective ([Quotients](#quotients)).

## Type equality is a proposition too

The `∈` slot admits large types and the top universe, so
`(A ≡ B ∈ 𝕌) : Ω` is an ordinary proposition and a type-equality
hypothesis is an ordinary context entry. Reflection applies at the type
level exactly as it does at the element level; there is no separate
type-equality judgement to learn and no coercion to insert.

## The price, and what you pay it with

Reflection makes type checking undecidable. Nova does not respond with a
search: an equation the checker cannot derive is **assumed and
reported** ([Reading the report](#report)). The practical consequence is that proofs feel
less like construction and more like *supplying the right facts in the
right scope*.

There is a second, smaller price. `≡` lives at `Ω`, and `Ω` has no
`𝕌`-code, so equational content cannot be stored inside a small type —
you cannot put a proof of `x ≡ y` into a Σ-code and keep the code
small. Where that is genuinely needed, `id.nova` gives the structural
counterpart:

```nova
data [a : 𝕌] ( Id : a → a → U
     ; refl : (x : a) → El (Id x x) )
```

`Id` is a code, so it can sit inside other codes and serve as an
eliminator motive, and the two notions are logically equivalent —
`idToEq` and `eqToId` bridge them, which is all a proposition can
soundly give. This is why the algebra modules state their laws with
`Id`: `IsMonoid` has to be a `𝕌`-family to be passed around as data.

## `≡` versus `≐`

You write `≡`; the report prints `≐`.

- `≡` is the surface proposition — something you state and prove.
- `≐` is judgemental equality — the checker's own notion, which is what
  an obligation is stated in.

They are connected in one direction by reflection (a proof of `≡` gives
`≐`) and in the other by `⋆` (a derivable `≐` inhabits the `≡`). When
you turn a reported obligation into a lemma, you are transcribing a `≐`
statement into an `≡` type; that transcription is mechanical, and the
report's context prefix becomes your Π-binders.

## Where to go next

- [Types without coherence](#coherence) for the payoff: dependent
  types stated and proved without a single cast.
- [Propositions and squashing](#propositions) for `Ω` itself: squashing, the connectives, and what may
  be eliminated into what.
- [Calc chains](#calc-chains) for `≡⟨ ⟩` chains, the readable way to do several steps.
- [The discharge engine](#discharge) for what `⋆` actually triggers.
- `src/nova/equality.nova` for the complete toolkit, and
  `src/nova/uip.nova` for the consequences of proof irrelevance.
