# Recursion and eliminators

This is the chapter where Nova stops resembling the language you came
from. You cannot write a recursive function. Not "you should not", or
"the termination checker might complain" — the name of a definition is
not in scope inside its own body:

```nova-sketch
def loop : ℕ → ℕ ≔ λn. loop n
```

```text
Error: def loop: unknown name 'loop'
```

## Why

A function that never returns would prove anything at all. Give me a
`loop : (n : ℕ) → n ≡ S n` and I will hand you a proof that `0 ≡ 1`,
and from there — by the argument in [Sums](#sums) — an inhabitant of
`𝟘`, and from there anything whatsoever. In a language where types are
claims, non-termination is not a bug that costs you a hung process; it
is a contradiction that costs you the whole system.

Other proof assistants accept recursive definitions and then police
them with a termination checker: a separate analysis that tries to
find a decreasing argument, and rejects what it cannot see. Nova does
not have one, because it does not need one. Recursion comes in shapes
that cannot loop, and everything else is spelled with those.

## The eliminator

Every type comes with one — `ℕ-elim` for naturals, `⊎-elim` for sums,
and one per sort for the types you declare. It packages "look at which
constructor this is, and here is what to do for each" together with
"and the recursive calls have already been made".

For `ℕ`:

```nova-sketch
ℕ-elim  z  (k ih. s)  n
```

- `z` is the result when `n` is zero;
- `(k ih. s)` is the result when `n` is `S k` — `k` is the
  predecessor, and **`ih` is the answer for `k`**, already computed;
- `n` is the number being taken apart.

`ih` is where the recursion lives. You never call yourself; you are
*handed* the result of the smaller case. That is why this cannot
loop — there is no call to get wrong — and why every use of it
terminates by construction.

Addition, for instance, is one step: the answer for `Z` is the other
argument, and the answer for `S k` is the successor of the answer for
`k`:

```nova
def plusByHand : ℕ → ℕ → ℕ ≔ λm. λn. ℕ-elim n (k ih. S ih) m
```

## Over your own types

The shape is the same, with one method per constructor. For the `List`
of [the previous chapter](#own-types):

```nova
def length : (a : 𝕌) → List a → ℕ using (List.unfold) ≔
  λa. λl. ListElim a (λw. ℕ) Z (λx. λr. λih. S ih) l
```

Reading the arguments in order: the parameter `a`; the **motive**
`(λw. ℕ)`, which says what the result type is; the method for `nil`,
which is `Z`; the method for `cons`, which receives the head `x`, the
tail `r` and the answer for the tail `ih`; and finally the list.

Note that the `cons` method gets both the tail *and* the answer for
the tail. You choose which you need — `length` uses only `ih`, while
something like "is this list sorted" would use both.

And it computes:

```nova
def lengthTwoZeros : length _ twoZeros ≡ 2
  using (List.eq, ListElim.eq, cons.eq, length.eq, nil.eq, twoZeros.eq) ≔
  ⋆
```

That is a closed computation, so `⋆` closes it — once the licences let
the definitions involved unfold. The long `using` clause is
characteristic of a fully closed calculation, and
[`using`: licences and scope](#using-clauses) explains how to arrive
at one without guessing.

## The motive

The motive is the argument with no counterpart in ordinary
programming. It says what the eliminator *produces*, as a function of
the value being taken apart — and because it may vary with that value,
the result type of the `nil` case and the result type of the `cons`
case need not be the same.

When the result type is constant, as in `length`, the motive is a
constant function and adds nothing but noise. For `ℕ-elim` you may
drop it entirely:

```nova
def zeroPlusId : (n : ℕ) → Z + n ≡ n using (+.eq, nat.plusZeroId) ≔ λn. ℕ-elim ⋆ (k ih. ⋆) n
```

That spelling is checking-only — the motive comes from the type the
whole expression is checked against, so it works exactly when the
checker already knows what you are producing
([Checking and inference](#bidirectional)). The corpus uses it almost
everywhere.

Where the motive earns its keep is when it is an **equation**. Then
`ih` is not a value but a *hypothesis*, and the eliminator is an
induction proof — which is [its own chapter](#induction-proofs), and
the reason this one matters more than it looks.

## When this is uncomfortable

Structural recursion covers more than it first seems, but the
translation can be tedious: an accumulator has to become a motive that
returns a function, and a two-argument recursion has to pick which
argument it eliminates. [Defining equations](#clausal-defs) gives you
the familiar clause syntax back, and compiles it to exactly the
eliminator you would have written.

What genuinely does not fit — a search that terminates for a reason
the shape of the data does not show — needs the termination argument
made explicit, by recursing on a bound. That is a real cost, and the
honest answer is that it is the price of the guarantee.
