# Sums

`A ⊎ B` is the disjoint union: a value is *either* an `A` or a `B`,
and you can always tell which. It is how a type offers a choice, and
together with pairs it is enough to build every finite data shape you
would reach for.

## Building

Two injections tag which side you are on:

```nova-sketch
inj₁ x     -- x : A,  so inj₁ x : A ⊎ B
inj₂ y     -- y : B,  so inj₂ y : A ⊎ B
```

They are checking-only: `inj₁ x` cannot know what `B` is, so the
expected type has to supply it. In practice this is invisible — you
write `inj₁ x` where an `A ⊎ B` is wanted and it works — but it is
why an injection cannot appear where the checker has nothing to check
it against ([Checking and inference](#bidirectional)).

`⊎` binds **tighter** than `→` and `⨯`, so `A ⊎ B → C` means
`(A ⊎ B) → C`, which is the reading you want. That is the opposite of
the trap in [Pairs](#pairs) — Nova follows Agda's convention here.

## Taking apart

`⊎-elim` handles both cases:

```nova
def swap : {a b : 𝕌} → a ⊎ b → b ⊎ a ≔ λa. λb. λt. ⊎-elim (x. inj₂ x) (y. inj₁ y) t
```

Read the arguments left to right: the left case `(x. inj₂ x)`, binding
the `A` inside; the right case `(y. inj₁ y)`, binding the `B`; then
the value being taken apart. Each case is a *binding group*, not a
λ — the name before the `.` is bound in the body that follows.

Unlike `ℕ-elim`, there is no induction hypothesis, because a sum is
not recursive. Case analysis is all there is.

## It computes

Applying the eliminator to an injection reduces to that case, on the
nose, so the two β-laws are proved by `⋆`:

```nova
def swapBeta1 : (a b : 𝕌) (x : a) → swap (inj₁ x) ≡ inj₂ x ∈ b ⊎ a using (sum.swap.eq) ≔
  λa. λb. λx. ⋆
```

The `swap.eq` licence lets `swap` unfold; after that both sides are
the same term.

## Case analysis is also proof

Here is the move that makes `⊎-elim` more than a `case` statement.
Give it a motive that is an *equation*, and the same eliminator
becomes a proof by cases:

```nova
def swapInvol : (a b : 𝕌) (t : a ⊎ b) → swap (swap t) ≡ t using (sum.swap.eq) ≔
  λa. λb. λt. ⊎-elim (x. ⋆) (y. ⋆) t
```

`swap` is an involution. The proof is: look at which side `t` is on;
in each case both sides compute to the same thing, so `⋆`. That is
exactly how you would argue on paper, and it is the shape every proof
about a sum takes.

## Injectivity and disjointness are theorems

Two facts about sums are built into most languages' pattern matching:
that `inj₁ x = inj₁ x'` implies `x = x'`, and that `inj₁ x` is never
`inj₂ y`. In Nova neither is a rule. Both are *derived*, in a dozen
lines of `sum.nova`, from what you already have.

Injectivity comes from building a retraction — a function that gets
the payload back out — and applying congruence:

```nova
def outl : (a b : 𝕌) → a → a ⊎ b → a ≔ λa. λb. λd. λt. ⊎-elim (x. x) (y. d) t
```

```nova
def inj1Injective : (a b : 𝕌) (x x' : a) → (inj₁ x ≡ inj₁ x' ∈ a ⊎ b) → x ≡ x' using (sum.outl.eq) ≔
  λa. λb. λx. λx'. λh. cong (λw. a) (outl _ b x) h
```

Disjointness is prettier, and is the first place the trick from
[The built-in types](#base-types) pays off. Define a function from the
sum to *types* — `𝟙` on the left, `𝟘` on the right:

```nova
def isLeftCode : (a b : 𝕌) → a ⊎ b → 𝕌 ≔ λa. λb. λt. ⊎-elim (x. 𝟙) (y. 𝟘) t
```

Now suppose `inj₁ x ≡ inj₂ y`. Transporting along that equation turns
an inhabitant of `isLeftCode … (inj₁ x)` — that is, of `𝟙` — into an
inhabitant of `isLeftCode … (inj₂ y)`, that is, of `𝟘`. So hand it
`()` and you are done:

```nova
def inj1NotInj2 : (a b : 𝕌) (x : a) (y : b) → (inj₁ x ≡ inj₂ y ∈ a ⊎ b) → 𝟘
  using (sum.isLeftCode.unfold) ≔
  λa. λb. λx. λy. λh. transport (isLeftCode a b) h ()
```

It is worth pausing on what just happened. A *false equation between
data* became a *false statement about types*, and then an inhabitant
of the empty type — using nothing but a function into `𝕌` and the fact
that equations transport. This is the standard way to refute an
equation in Nova, and it works for any two constructors of any type
you define.

## What `⊎` is not

`⊎` is **non-dependent**: there is no binder form, and the right-hand
type cannot mention anything about the left. If you need a choice
whose branches carry different, related information, that is a `data`
declaration ([Defining your own types](#own-types)), not a sum.
