# Introduction

Nova is a programming language in which you can also *prove things* —
and the proving uses the same file, the same syntax and the same `def`
keyword as the programming. A theorem is a type. Its proof is a value
of that type. There is no second language for proofs, and no point at
which you stop programming and start proving.

This book teaches the **surface language**: the text you write in a
`.nova` file. It assumes you have written programs in a functional
language — algebraic data types, pattern matching, recursion — and
that you are comfortable with ordinary mathematical writing, including
proof by induction. It assumes **nothing** about dependent types or
proof assistants.

> If you already know Agda, Idris or Coq, [Nova for Agda
> users](#agda-map) is a faster way in, and you can read it before
> anything else.

## Start with a program

Here is a definition. Nothing about it should surprise you:

```nova
def plus : ℕ → ℕ → ℕ
  | plus Z n ≔ n
  | plus (S m) n ≔ S (plus m n)
```

`ℕ` is the natural numbers, built from `Z` (zero) and `S` (successor).
`≔` is "is defined as", `→` is the function arrow, and the two lines
beginning with `|` are clauses matched in order — addition by
recursion on the first argument, exactly as you would write it
anywhere else. Definitions build on each other in the usual way:

```nova
def double : ℕ → ℕ
  | double n ≔ plus n n
```

The general shape of a definition is `def name : type ≔ body`; the
clause form above is a convenience that expands into it
([Defining equations](#clausal-defs)). If the glyphs are the obstacle
rather than the ideas, [Reading and typing Nova](#notation) is the
chapter that fixes that, and it comes before anything you have to
write yourself.

## Types that talk about values

Here is where Nova departs from the languages you know. A type may
mention a *value*:

```nova
def vappend : (n : ℕ) {A : 𝕌} (m : ℕ) → vect n A → vect m A → vect (n + m) A
```

`vect n A` is the type of vectors of length `n` holding elements of
`A` — not one type but a whole family, one for each length. Read the
last part of that signature aloud: given a vector of length `n` and a
vector of length `m`, this returns a vector of length `n + m`. (The
braces around `{A : 𝕌}` mark an argument the checker works out for
itself, and `𝕌` is the type *of* types; both are chapters of their
own, and neither is the point here.)

The length is no longer a fact you keep in a comment or check at run
time. It is *in the type*, and a definition of `vappend` that got the
length wrong would not be a definition of `vappend` at all — it would
fail to typecheck. That is what **dependent types** means, and it is
the whole reason the rest of this book exists. Chapter
[What dependent types are](#dependent-types) develops the idea
properly; [Indexed families](#indexed-families) builds vectors from
scratch.

## A proof is a value

Once a type can mention values, a type can *state something*:

```nova
def plusZr : (n : ℕ) → plus n Z ≡ n using (definingEq.plusZ, plus.eq) ≔ λn. ℕ-elim ⋆ (k ih. ⋆) n
```

Read the type: **for every** natural number `n`, `plus n Z` equals
`n`. That is a theorem — the sort of thing you prove by induction. And it is written as a type, because:

- `(n : ℕ) → …` is a function type, and a function that works for
  every `n` is exactly what "for all `n`" means;
- `≡` builds a statement out of two values;
- so a **value** of that type is a proof of the statement.

Everything after `≔` is that value. `ℕ-elim` is induction
([Proving by induction](#induction-proofs)), and `⋆` is the one proof
there is: writing it asks the checker to see for itself that the two
sides are equal ([Reflection](#reflection)). The
`using (…)` clause names the facts this proof is allowed to use, which
is a habit worth noticing early and understanding later
([`using`: licences and scope](#using-clauses)).

The point is not the details. The point is that `plusZr` is an
ordinary definition. It sits in the same file as `plus` and `double`,
it is written with the same keyword, and the checker treats all three
the same way.

## What the checker actually does

It checks that the value you wrote has the type you claimed. That is
all it does. It does not search for proofs on your behalf, it does not
guess what you meant, and it does not run your program.

So there are two outcomes. Either the file is **accepted** — the run
names each definition as it goes and ends with the single word
`Accepted.` — or the checker reports what it could not establish.
Suppose you claim something false:

```nova
def bad : Z ≡ S Z ∈ ℕ ≔ ⋆
```

(`∈ ℕ` says which type the two sides are being compared in.) You get
this:

```report
open obligations (1):
  [1] ⊢ Z ≐ S Z : ℕ
      at: input.nova:3:25: def bad: checking ⋆
```

Read it as: *at the `⋆` in `def bad`, I needed `Z` and `S Z` to be the
same natural number, and I could not derive that.* Which is fair,
since they are not. (The report writes `≐` for its own notion of
"the same"; you write `≡` for the statement. The difference matters
later and not yet.)

An **obligation** is the checker's way of saying "I had to assume
this." It is not always a bug: very often it is something true that
needs a lemma you have not written yet. A file is accepted only when
the list is empty, and getting it there — read the obligation, prove
it, name it, re-run — is the working rhythm of Nova.
[Reading the report](#report) is the chapter on this, and
you will want it early.

## Five things to know before you start

None of these will be obvious from a language you already know.

1. **Everything terminates.** There is no general recursion and no
   termination checker; instead, recursion has shapes that cannot loop
   ([Recursion and eliminators](#recursion)). A function that ran
   forever would prove anything, and so the language does not offer
   one.
2. **A proved equation becomes invisible.** Once you have a proof that
   `a` equals `b`, the checker treats `a` and `b` as interchangeable
   wherever that proof is in scope — you never "apply" it
   ([Reflection](#reflection)). This one rule is responsible for most
   of what makes Nova's proofs short.
3. **The checker will ask you for things.** Because of rule 2, it
   cannot always decide equality, so it reports rather than guesses.
   Obligations are a normal part of writing a file, not a failure
   mode.
4. **Every definition names what it uses.** Facts do not float in
   scope; an item lists the lemmas its checking may draw on. The
   result is that an accepted file is a self-contained record of *why*
   it is accepted ([The discharge engine](#discharge)).
5. **Your program is checked twice.** The elaborator is clever and
   untrusted; it emits a certificate that a small, auditable kernel
   re-checks. A bug in the clever part can cost you a proof that
   should have gone through — never a wrong acceptance
   ([Tooling](#tooling)).

Some things you may expect are simply absent: there is no tactic
language, no instance search or type classes, no hierarchy of universe
levels, and no record syntax (structures are nested pairs). Where a
familiar tool is missing, the chapter that would have used it says
what to do instead.

## How to read this book

- **New to all of this** — read Parts I to V in order. They are
  written to be read that way, and each chapter assumes the ones
  before it.
- **Here to write programs, not proofs** — Parts I to IV are a
  complete tour of the language as a programming language.
- **Coming from a proof assistant** — start with
  [Part VII](#agda-map), then dip into Parts III to VI for the parts
  that differ.
- **Looking something up** — Part IX is grammar, precedence, generated
  names, the library, tooling and a glossary.

## Conventions

- Every Nova snippet in this book is **real code, quoted verbatim**
  from `src/nova` or from the test suite, and a test checks that it
  stays that way. If you copy a snippet, you are copying something the
  implementation has accepted.
- Occasional snippets that illustrate a point rather than come from
  the corpus are marked as such in the source and are the exception.
- Names in code font like `el-reflect` are rules of the underlying
  theory; you can look them up on the [specs page](specs.html). This
  book is *not* normative — where it and a spec disagree, the spec is
  right.
- Citations like `src/nova/nat.nova` name real files, and you can read
  them [rendered and highlighted](nova/index.html).
