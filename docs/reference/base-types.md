# The built-in types

Three types come with the language. Everything else — booleans, lists,
vectors, the integers, the reals — is defined in a file, using the
machinery of the next few chapters. This one is about the three you
get for free, and they are chosen for what they let you *build*, not
for what you can do with them directly.

## `𝟘`, the empty type

`𝟘` has no values at all. You can never produce one, which makes it
useless as data and precisely useful as a *claim*: a function into
`𝟘` says its argument cannot exist.

Its eliminator says the same thing from the other side. Given a value
of `𝟘` — which you can only ever have hypothetically — you may produce
anything you like:

```nova
def absurd : 𝟘 → ℕ ≔ λx. 𝟘-elim x
```

Read `𝟘-elim x` as "from the impossible, anything". This is how
refutation works: `¬ A` is `A → 𝟘` ([And, or, not](#connectives)),
and a proof of it is a function that turns a hypothetical `A` into an
inhabitant of a type with none.

## `𝟙`, the unit type

`𝟙` has exactly one value, written `()`:

```nova
def unit : 𝟙 ≔ ()
```

More than that, the checker *knows* it has one value, so any two
inhabitants are equal without your having to say why:

```nova
def unitIsUnique : (x y : 𝟙) → x ≡ y ≔ λx. λy. ⋆
```

No licence, no induction — `⋆` closes it. `𝟙` is what you use when
something is required by a type but carries no information: the
payload of a case that has nothing to say, or the "true" of a
proposition.

## `ℕ`, the natural numbers

`ℕ` is built from two constructors: `Z` for zero, and `S` for
successor. Decimal literals are sugar for towers of them, so `5` and
`S 4` are not merely equal but *the same term*:

```nova
def five : ℕ ≔ 5

def fiveIsSuccFour : 5 ≡ S 4 ≔ ⋆
```

To take a natural apart you use its eliminator, `ℕ-elim`, which is
[the next chapter but one](#recursion). Its simplest use is worth
seeing now, because it shows something a functional programmer does
not expect — a function returning a **type**:

```nova
def isZero : ℕ → 𝕌 ≔ λn. ℕ-elim 𝟙 (k ih. 𝟘) n
```

`isZero Z` is `𝟙`, which has an inhabitant; `isZero (S k)` is `𝟘`,
which has none. So this one definition turns a number into the claim
"you are zero", true or false by *inhabitation*. That trick — a
recursively computed type — is how `𝟘` and `𝟙` earn their place, and
it is the seed of everything in
[Types that depend on values](#dependent-types).

## Why so few

Most languages build in far more: booleans, characters, strings,
machine integers. Nova builds in almost nothing, because
[the `data` item](#own-types) can define these as ordinary code, and
anything defined that way comes with an induction principle and
computation rules the checker already understands. A built-in `Bool`
would buy nothing that

```nova-sketch
data ( Bool : U ; true : El Bool ; false : El Bool )
```

does not, and would cost a special case in every part of the system.
