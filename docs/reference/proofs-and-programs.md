# Proofs, programs, and what a checker is for

Chapter 1 claimed that a theorem is a type and a proof is a value.
This chapter is why that is a fact rather than a slogan, what it looks
like in code you have already written, and — just as important — what
a proof checker does *not* give you.

There is no new syntax here. If you would rather get your hands dirty
first, [Installing and running Nova](#installation) and
[Your first file](#first-file) are next, and this chapter will keep.

## A type is a specification

How much does this promise?

```text
sort : List ℕ → List ℕ
```

Almost nothing. Reversing the list has that type. Returning the input
untouched has that type. Returning the empty list has that type. The
type rules out returning a string, and that is about the extent of it.

Now suppose the type could also say *the output is sorted*, and *the
output is a permutation of the input*. Those two facts happen to pin
`sort` down completely: any function satisfying both is a sorting
function, and no amount of cleverness or carelessness inside the
definition can produce something else that typechecks.

So a type is a specification, and specifications come in strengths.
The question is what stops you writing the stronger one, and the
answer is that "is sorted" and "is a permutation of" are statements
about *values* — so the type would have to mention values. That is
exactly what dependent types allow, and it is why the language has
them.

> You do not have to go all the way, and most Nova files do not. The
> strength of a specification is a choice you make definition by
> definition.

## Propositions are types

Here is the dictionary that makes it work. Read the middle column as
the type you would write, and the right column as what a value of that
type *is*.

| To say | Write | A value of it is |
| --- | --- | --- |
| A and B | `A ⨯ B` | a pair: a proof of each |
| A implies B | `A → B` | a function taking a proof of A to a proof of B |
| for every `x : X`, `P x` | `(x : X) → P x` | a function taking each `x` to a proof of `P x` |
| there is an `x : X` with `P x` | `(x : X) ⨯ P x` | a pair: a witness, and a proof about it |
| false | `𝟘` | nothing at all — the type is empty |
| true | `𝟙` | the single value `()` |
| not A | `A → 𝟘` | a way to turn a proof of A into an absurdity |

Three of those are worth saying out loud.

**Implication is a function.** To prove "A implies B" you must be able
to take *any* evidence for A and produce evidence for B. A procedure
that transforms evidence into evidence is a function; there is nothing
else it could be.

**"For every" is a function too** — one whose result *type* changes
with the argument. That is the only genuinely new idea in the table,
and it is the one dependent types supply.

**Negation is not primitive.** To refute A is to show that a proof of
A would let you build an inhabitant of the empty type — and since
there are none, there must be no proof of A either.

## You have already written proofs

```nova
def id : {A : 𝕌} (x : A) → A ≔ λA. λx. x
```

As a program, that is the identity function. As logic, read the type:
for any `A`, `A` implies `A`. The identity function is the proof, and
it is the only sensible one.

```nova
def const : {A B : 𝕌} (x : A) (y : B) → A ≔ λA. λB. λx. λy. x
```

As a program, the function that ignores its second argument. As logic:
*A implies that B implies A* — a tautology, proved by a function you
have written a hundred times without thinking of it as a proof.

Nothing about the code changed between those two readings. This
correspondence has a name — Curry–Howard — which is worth knowing and
is not the point. The point is that your existing instincts about
building and composing functions are, already, instincts about
building and composing proofs.

## Evidence you can carry

Existence is where the correspondence gets its teeth. Here is a type
whose values are natural numbers *carrying evidence about themselves*:

```nova
def OnlyZ : 𝕌 ≔ (n : ℕ) ⨯ Id _ n Z
```

Read it as: a number `n`, paired with evidence that `n` is `Z`.
(`Id _ n Z` is the statement "`n` equals `Z`" in a form that can sit
inside another type — [Equality](#equality) explains why there are two
spellings — and the `_` is an argument the checker fills in for
itself.) An inhabitant must supply both halves:

```nova
def onlyZ : OnlyZ using (id.Id.eq, id.OnlyZ.unfold) ≔ Z, refl ℕ Z
```

The witness `Z`, then the evidence. To claim that something exists,
you hand over the thing — there is no way to assert existence without
producing a witness. That is what people mean when they call this kind
of system **constructive**.

Refutation is the mirror image:

```nova
def inj1NotInj2 : (a b : 𝕌) (x : a) (y : b) → (inj₁ x ≡ inj₂ y ∈ a ⊎ b) → 𝟘
```

Ignore the details of the first three arguments; read the tail. *Given
a proof that these two things are equal, produce an element of the
empty type.* That is precisely what "they are different" means here,
and it is a theorem rather than a built-in fact.

## What the checker guarantees

The checker verifies exactly one thing: that the value you wrote
inhabits the type you claimed. From that one thing follows a real
guarantee, and three real limits that are worth internalising before
you start trusting output.

**The guarantee.** If a file is accepted, every theorem stated in it
has a proof that has been mechanically verified. There is no "mostly",
no "except for the tricky case", and no reliance on you having been
careful.

**Limit one: you still have to read the statement.** The checker has
no idea what you *meant*. A flawless proof of the wrong theorem is
worth nothing, and nothing in the system will tell you it is the wrong
theorem. This is why so much of Nova's design effort goes into keeping
statements short and readable: the types are the part a human must
audit, and they are the only part.

**Limit two: vacuous truth is truth.** A theorem whose hypotheses can
never be satisfied is provable and says nothing. If you assume
something impossible, everything you derive from it is uninformative
rather than wrong — and it will pass.

**Limit three: something is always trusted.** Namely the kernel and
the theory it implements. Nova's answer is to keep that base small and
auditable, and to re-check the clever, untrusted parts against it —
but "verified by machine" always means "verified by *that* machine".

One thing that is *not* a limit: you cannot quietly assume a lemma to
get moving. A definition without a body is reported, an equation the
checker had to assume is reported, and neither an accepted file nor a
silent workaround exists while either is outstanding.

## Is it worth it

Sometimes. Being honest about when:

- **Worth it** when a claim quantifies over more cases than you can
  test, when an invariant has to survive years of refactoring, when
  the argument is too intricate to eyeball, or when being wrong is
  expensive.
- **Not worth it** for code a good test suite already pins down, or
  for anything you are about to throw away.

And the cost is real. Expect to spend more time stating lemmas than
writing programs, and expect the checker to be a pedantic reader.
Nova's specific bet on lowering that cost is
[Reflection](#reflection) and [The discharge engine](#discharge) —
whether it pays off is a judgement you will be able to make for
yourself by the end of Part VI.

## One refinement, flagged early

The dictionary above is the general picture, shared by every system of
this kind. Nova adds a wrinkle that will save you confusion later:
some types are **propositions**, meaning their inhabitants carry no
information whatsoever, so any two proofs of one are interchangeable.
Equality is one of them.

For those types, "which proof did you use?" is not a question that can
be asked — which is exactly why Nova's proofs about equations can be
as short as they are. The existential pair above is the *informative*
kind, whose witness you can project back out; there is a forgetful
version too. [Propositions](#propositions) is where that story starts.
