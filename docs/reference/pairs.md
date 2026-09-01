# Pairs

A pair holds two values. This chapter is the non-dependent case, where
the two are independent; when the type of the second may *mention* the
first you get [Σ-types](#sigma-types), which is the same construct
with the restriction lifted.

## Building and taking apart

`A × B` is the type, `,` builds, and `.π₁` and `.π₂` project:

```nova
def swap : (ℕ × 𝟙) → 𝟙 × ℕ ≔ λp. p .π₂ , p .π₁
```

```nova
def firstOfTwo : (ℕ × 𝟙) → ℕ ≔ λp. p .π₁
```

Note the space in `p .π₁`. The projections are postfix and bind
tightly, so `f p .π₁` is `f` applied to `p .π₁` — parenthesise when
you mean the other reading.

`,` is right-associative, so `a , b , c` is `a , (b , c)`: a triple is
a pair whose second component is a pair, and nested pairs need no
brackets. Nova has no n-ary tuples and no records; a structure with
five fields is four nested pairs, and [Σ-types](#sigma-types) shows
how the corpus makes that pleasant.

## Precedence

`×` binds tighter than `→` and tighter than `⊎`, so the readings are
the ones you would guess:

| Written | Means |
| --- | --- |
| `A × B → C` | `(A × B) → C` |
| `A ⊎ B × C` | `A ⊎ (B × C)` |
| `A × B × C` | `A × (B × C)` |

Product beating sum matches the arithmetic the notation is borrowed
from, and matches Nova's own operators, where `*` binds tighter than
`+`. The examples above parenthesise `(ℕ × 𝟙)` anyway, which is never
wrong and is often kinder to a reader.

There is one place `×` does *not* stop where you expect. The **binder**
form, `(x : A) × B`, sits beside `→` and takes its body maximally, so
everything after it belongs to the pair — which is what keeps the
record idiom in [Σ-types](#sigma-types) readable, and means
`A × B` is not merely shorthand for `(_ : A) × B`. A `×` whose
right-hand side is an arrow, an equation or a quotient needs
parentheses: `P × ((x : G) → Q)`.

## η: a pair is its projections

Rebuilding a pair from its own two halves gives back the pair, and the
checker will confirm it — if the item asks:

```nova
def pairEta : (p : ℕ × 𝟙) → (p .π₁ , p .π₂) ≡ p using (sigma.eta) ≔ λp. ⋆
```

The `sigma.eta` licence is the interesting part. This is a *judgemental*
law, not a theorem you prove by cases — there is no case analysis on
pairs to do — but like unfolding a definition it is something the item
must ask for ([`using`: licences and scope](#using-clauses)). Without
it you get an obligation reading `p .π₁, p .π₂ ≐ p`, which is a
confusing thing to stare at until you know that the fix is a licence
rather than a proof.

Once licensed, it makes round trips free:

```nova
def roundTrip : (p : ℕ × 𝟙) → unswap (swap p) ≡ p using (sigma.eta, swap.eq, unswap.eq) ≔ λp. ⋆
```

`⋆`, with no induction: unfold the two functions, and η closes what is
left.

There is a matching licence for functions, `pi.eta`, which says
`λn. f n` is `f`. The two come up in the same situations and are
mentioned together throughout the book.

## What pairs are for

Beyond the obvious "two results at once", the pattern that matters
later is **a value together with evidence about it** — a number and a
proof that it is even, a list and a proof that it is sorted. That
needs the second component's type to mention the first, which is
exactly what [Σ-types](#sigma-types) allows, and it is how
specifications get attached to data in Nova.
