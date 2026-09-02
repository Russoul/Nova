# Defining equations

Writing every function as an eliminator gets old. The clause form
gives you back the spelling you are used to — and, because Nova cannot
simply take your word for it, gives you rather more besides.

## The syntax

```nova
def plus : ℕ → ℕ → ℕ
  | plus Z n ≔ n
  | plus (S m) n ≔ S (plus m n)
```

Each clause opens with `|`, and the head must be the **item's own
name** — `| g Z ≔ …` inside `def f` is a parse error, not a nested
definition. Patterns are constructor spellings and variables. A single
clause with no split at all is fine:

```nova
def double : ℕ → ℕ
  | double n ≔ plus n n
```

An operator-named item may be written infix, once it has a fixity:

```nova
infixl 6 ⊞
def ⊞ : ℕ → ℕ → ℕ [oplusEta]
  | Z ⊞ n ≔ n [oplusZ]
  | S m ⊞ n ≔ S (m ⊞ n) [oplusS]
```

## What it expands into

The clause form is a macro, and it produces **three** things, not one:

1. the definition itself, compiled to the eliminator you would have
   written by hand;
2. one **equation** per clause — the clause, restated as a provable
   fact;
3. a **uniqueness** lemma: anything satisfying those equations *is*
   this function.

The checker names them as it goes:

```report
defined plus by clauses (plus, plusZ, plusS, plusEta)
```

`plusZ` and `plusS` are the two clauses as equations; `plusEta` is
uniqueness. By default they are the item's name with the constructor
appended, and `Eta` for the last; the `[name]` brackets above override
that, which an operator-named item needs since `⊞Z` is not a name you
could write.

## Why the equations exist

Because the definition is compiled away. Once `plus` is an `ℕ-elim`
term, "the first clause says `plus Z n` is `n`" is not something the
checker can see by looking — so the macro proves it and hands it to
you as a lemma. That is the `plusZ` you cited in
[Your first file](#first-file), and it is why the report's hint
suggested it:

```nova
def plusZr : (n : ℕ) → plus n Z ≡ n using (definingEq.plusZ, plus.eq) ≔ λn. ℕ-elim ⋆ (k ih. ⋆) n
```

The uniqueness lemma is the one with no counterpart elsewhere. It says
your clauses **determine** the function: any candidate satisfying them
is equal to it, pointwise. That turns the clauses from an
implementation into a specification, and it is what lets you swap a
definition for a hand-written one and prove the two agree:

```nova
def plusByHand : ℕ → ℕ → ℕ ≔ λm. λn. ℕ-elim n (k ih. S ih) m

def byHandIsPlus : (m n : ℕ) → plusByHand m n ≡ plus m n using (definingEq.plusByHand.eq) ≔
  λm. λn. plusEta plusByHand (λx. ⋆) (λk. λx. ⋆) m n
```

Read the proof: hand `plusEta` the candidate and a proof of each
clause, and it gives back "they are the same function".

## The structural fragment

Clauses are compiled, and what can be compiled is a fragment. In it:

- **splitting one column** — the patterns differ in a single argument
  position, at depth one;
- **recursion on the split argument**, as `plus` does;
- **recursion at a changed trailing argument** — an accumulator:

```nova
def addAcc : ℕ → ℕ → ℕ
  | addAcc Z n ≔ n
  | addAcc (S m) n ≔ addAcc m (S n)
```

- **splitting a sum** instead of a natural:

```nova
def swap : ℕ ⊎ 𝟙 → 𝟙 ⊎ ℕ
  | swap (inj₁ n) ≔ inj₂ n
  | swap (inj₂ u) ≔ inj₁ u
```

- **recursive calls nested inside other applications**:

```nova
def mul : ℕ → ℕ → ℕ
  | mul Z n ≔ Z
  | mul (S m) n ≔ plus n (mul m n)
```

## Outside the fragment

Step outside it — split two columns, or leave a case out — and Nova
does something better than rejecting you:

```report
declared f and its equations (f, fZ, fEta) — clauses outside the structural fragment [+3 declarations]
```

```report
open declarations (3):
  [f] ⊢ ? : ℕ → ℕ
      at: input.nova:5:5: def f
  [fZ] ⊢ ? : f Z ≡ Z ∈ ℕ
      at: input.nova:6:3: def fZ
  [fEta] ⊢ ? : (x:ℕ → ℕ) → (x Z ≡ Z ∈ ℕ) → (n:ℕ) → (x n ≡ f n ∈ ℕ)
      at: input.nova:5:5: def fEta
```

The macro could not build the function, so it wrote down the
**contract** instead: here is the function you asked for, here is each
equation it must satisfy, here is the uniqueness property. All three
are now declarations you owe ([Definitions](#definitions)), and you
supply them by hand. Nothing is lost and nothing is assumed — you have
gone from "write clauses and get a definition" back to "write a
definition", with the specification spelled out for you.

Note in passing what the incomplete split above really costs: not an
"inexhaustive patterns" warning, but an obligation to say what `f` is
on the case you omitted.

## The witness form

You can also supply the definition yourself *and* keep the clauses,
by writing both:

```nova
def pred : ℕ → ℕ ≔ λn. ℕ-elim Z (k ih. k) n
  | pred Z ≔ Z
  | pred (S m) ≔ m
```

```report
defined pred by clauses via witness (pred, predZ, predS, predEta)
```

Here the clauses are no longer the implementation — they are the
specification, checked against the definition you gave. Use it when
the compiled form would be inefficient or ugly, and you still want the
equations and the uniqueness lemma.

## Which to write

Use clauses when they fit; they are shorter and they generate the
lemmas you will end up citing anyway. Drop to a bare eliminator when
the recursion does not fit the fragment, or when the motive has to be
something specific — as it does in every proof by induction
([Proving by induction](#induction-proofs)).
