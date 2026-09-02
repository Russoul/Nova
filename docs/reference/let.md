# `let`

`let` names something inside an expression. It is the only form that
attaches a name to a *value* locally — λ binds arguments, but binds
them to nothing — and it does one thing the version in your favourite
language does not: the name stays **transparent**, so the checker
knows what it stands for.

## Syntax

```nova-sketch
let x ≔ e in body
```

The body extends maximally, exactly as a λ body does, so a `let` runs
to the end of the enclosing expression unless you parenthesise it.
`let`s nest, and the annotated form fixes the definiens' type:

```nova
def four : ℕ ≔ let one : ℕ ≔ S Z in let two ≔ one + one in two + two
```

`let x : T ≔ e in b` is sugar for `let x ≔ (e : T) in b` — the
annotation is an ascription on the definiens, not a separate feature.

A `let` is an ordinary expression and can appear anywhere one can,
including in the head position of an application:

```nova
def three : ℕ ≔ (let f : ℕ → ℕ ≔ λx. S x in f) 2
```

## Transparency

Here is what makes `let` worth a chapter. Inside the body, `x` is not
merely a variable of the right type: the body is checked knowing that
`x` **is** `e`. The definition travels with the binding.

The practical effect is that a fact stated about the abbreviation and
a fact stated about its unfolding are the same fact, with no work from
you:

```nova
def letShared : (n : ℕ) → n + n + Z ≡ n + n using (nat.plusCongL, nat.plusZeroId) ≔
  λn. let m ≔ n + n in (⋆ : m + Z ≡ m)
```

The goal of that definition is about `n + n`. The proof supplied is
about `m`. Nothing bridges the two — no rewriting, no transport, no
unfolding step — because the `let` binding carries the equation
`m ≡ n + n` into the body, and the checker uses it like any other
hypothesis in scope ([Reflection](#reflection)).

Note that this is *not* β-reduction. `m` is a variable, not a redex
waiting to be reduced; what closes the gap is the equation the binder
supplies.

## From outside, a `let` is its unfolding

The transparency does not stop at the definition's edge. To everything
downstream, a definition containing a `let` behaves exactly as if you
had written the expansion:

```nova
def fourUnfolds : four ≡ 4 using (letExpr.four.eq, nat.+.eq) ≔ ⋆

def threeUnfolds : three ≡ 3 using (letExpr.three.eq) ≔ ⋆
```

Both are `⋆`: once `four` may unfold, the `let`s inside it compute
away and what is left is a number. Using a `let` never costs a caller
anything, and never obliges you to prove a lemma about the
abbreviation.

## When to use it

- **To name a subterm the goal mentions repeatedly.** The name is
  shorter to read and to write, and transparency means it costs
  nothing.
- **To name a step in a long definition**, for the same reason you
  would in any language.
- **Not** to hide something. `let` is transparent by design; if you
  want an opaque name, a top-level definition is the thing that gives
  you one, since those do not unfold unless licensed
  ([Definitions](#definitions)).

## The whole of `letExpr.nova`

The corpus module for this chapter is five definitions long, and every
one of them appears above. If you want to see the feature exercised in
one screen, that is the file to read.
