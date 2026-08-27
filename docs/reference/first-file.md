# Your first file

Time to write something. By the end of this chapter you will have a
file that Nova accepts, containing two definitions and two proofs —
and, more usefully, you will have watched it *fail* twice and fixed
it, which is the part nobody can tell you about in the abstract.

Make a directory, open a file called `first.nova`, and follow along.

## A definition

Start with addition:

```nova
def plus : ℕ → ℕ → ℕ
  | plus Z n ≔ n
  | plus (S m) n ≔ S (plus m n)
```

Check it:

```bash
nova elab first.nova
```

```report
defined plus by clauses (plus, plusZ, plusS, plusEta)
```

The run reports one line per item. This one says the definition went
in *by clauses*, and lists four names: `plus` itself, plus three more
the clause form generated. `plusZ` and `plusS` are the two clauses
restated as equations — "`plus Z n` is `n`" and "`plus (S m) n` is
`S (plus m n)`" — and they will matter in a moment. `plusEta` you can
ignore until [Defining equations](#clausal-defs).

## Building on it

Definitions see everything above them:

```nova
def double : ℕ → ℕ
  | double n ≔ plus n n
```

A single clause with no case split is a perfectly ordinary
definition — the clause syntax does not oblige you to match on
anything.

## A first theorem

Now state something. Addition is defined by cases on its *first*
argument, so `plus Z n` ought to be `n` on the nose:

```nova
def plusZl : (n : ℕ) → plus Z n ≡ n ≔ λn. ⋆
```

Read the type as "for every `n`, `plus Z n` equals `n`", and the body
as "λ takes the `n`, and `⋆` asks the checker to see the rest". Run
it, and it does not work:

```report
  [1] (n : ℕ) ⊢ plus Z n ≐ n : ℕ
      at: def plusZl: checking ⋆
      hint: closes with plusZ
```

This is the moment worth slowing down for. The checker is not saying
your claim is false. It is saying: *at that `⋆`, I needed `plus Z n`
and `n` to be the same, and I could not get there.*

Why not? Because **definitions do not unfold by themselves**. `plus`
is a name, and the checker will not look inside it unless the item
says it may. That is a deliberate choice — it is what keeps checking
predictable and fast — and it is the single most common cause of a
first obligation.

Notice the last line, though. The checker went looking and found
something that *would* have worked, and told you its name: `plusZ`,
one of the equations the clause form generated. Take the hint:

```nova
def plusZl : (n : ℕ) → plus Z n ≡ n using (plusZ) ≔ λn. ⋆
```

The `using (…)` clause names the facts this item is allowed to draw
on. Now it goes through.

## A theorem that needs actual work

Try the mirror image — `plus n Z` instead of `plus Z n`:

```nova
def plusZr : (n : ℕ) → plus n Z ≡ n ≔ λn. ⋆
```

```report
  [2] (n : ℕ) ⊢ plus n Z ≐ n : ℕ
      at: def plusZr: checking ⋆
```

Same shape of report, one crucial difference: **no hint**. Nothing in
scope closes this one, and no licence would help.

That is not a limitation of the checker; it is the mathematics.
`plus` recurses on its first argument, so `plus Z n` collapses in one
step, while `plus n Z` cannot move at all until you know what `n` is.
The two statements look symmetric and are not. Proving the second one
takes induction — exactly as it would on paper:

```nova
def plusZr : (n : ℕ) → plus n Z ≡ n using (plusZ, plus.eq) ≔ λn. ℕ-elim ⋆ (k ih. ⋆) n
```

`ℕ-elim` is proof by induction on `n`: the first `⋆` is the base case
(`plus Z Z ≡ Z`), and `(k ih. ⋆)` is the step, where `k` is the
predecessor and `ih` is the induction hypothesis you are handed —
already proved, already in scope. Both cases are `⋆` because once the
hypothesis is available each side computes to the other.

The extra licence `plus.eq` lets this item unfold `plus` itself, which
the step case needs. Choosing what to put in a `using` clause is a
skill, and [`using`: licences and scope](#using-clauses) is where it
is taught; for now, adding what the report hints at and what the proof
obviously leans on will get you a long way.

## The finished file

```nova
def plus : ℕ → ℕ → ℕ
  | plus Z n ≔ n
  | plus (S m) n ≔ S (plus m n)

def double : ℕ → ℕ
  | double n ≔ plus n n

def plusZl : (n : ℕ) → plus Z n ≡ n using (plusZ) ≔ λn. ⋆

def plusZr : (n : ℕ) → plus n Z ≡ n using (plusZ, plus.eq) ≔ λn. ℕ-elim ⋆ (k ih. ⋆) n
```

```report
defined plus by clauses (plus, plusZ, plusS, plusEta)
defined double by clauses (double, doubleEq, doubleEta)
defined plusZl
defined plusZr
Accepted.
```

Four items, two of them theorems, and nothing in the file marks which
is which.

> Every line of that file and every line of those transcripts is
> checked by Nova's own test suite. If the language changes under this
> chapter, the chapter breaks and gets fixed.

## Working incrementally

You do not have to write a proof in one go, and you should not try.
Nova gives you three ways to leave a gap and ask what belongs in it.

### `⋆` is the hole

Nova has no `?goal` syntax. It does not need one, because `⋆` already
plays that role: it marks the spot where a proof is owed, and you can
ask what is owed there. With the language server running
([Editor support](#installation)), put the cursor on any `⋆` and
hover. You get its goal:

```text
⋆ : plus n Z ≡ n ∈ ℕ
```

Hover works whether or not the `⋆` succeeded, so this is also how you
inspect a goal you have already closed — useful when you want to know
*what* you just proved. Hovering a binder gives its type, and hovering
a `_` shows you what the checker inferred there and why.

### An unclosed goal prints itself

Without an editor you get the same information from the report,
because an obligation *is* the goal. Suppose the step case of that
induction had not gone through:

```report
  [1] (n : ℕ) (k : ℕ) (ih : plus k Z ≡ k ∈ ℕ) ⊢ plus (S k) Z ≐ S k : ℕ
      at: def plusZr: checking ⋆
```

Everything to the left of `⊢` is what you have to work with, and it is
worth reading slowly the first time. `k` is the predecessor, and
`ih : plus k Z ≡ k ∈ ℕ` is the induction hypothesis — the statement
one size smaller, handed to you as a hypothesis. To the right of `⊢`
is what you owe. That display is the whole of proof state in Nova, and
you can always get it by writing `⋆` and running the checker.

### State it now, prove it later

The third move is to write a definition with a type and **no body**:

```nova
def plusZr : (n : ℕ) → plus n Z ≡ n
```

That is a *declaration*. The name exists, everything below may use it,
and the checker keeps a list of what you still owe:

```report
declared plusZr [+1 declaration]
```

```report
open declarations (1):
  [plusZr] ⊢ ? : (n:ℕ) → (plus n Z ≡ n ∈ ℕ)
      at: def plusZr
```

Note the shape of that entry: a name, and the type of the thing you
have not written. It is a named hole at the scale of a whole
definition.

This is how to work top-down. Write the theorem you actually want,
declare the lemmas it needs, get the top-level proof to go through,
and only then fill the lemmas in — the checker keeps score, and the
file is not accepted while any declaration stands. There is no way to
forget one and no way to ship one by accident.

## What just happened

Three things are worth carrying forward.

**An obligation is a question, not a rejection.** Twice the checker
told you what it could not derive and where. Neither report was an
error, and neither was a bug in your file — one wanted a licence, the
other wanted a proof.

**The report tells you which kind you have.** A `hint:` line means the
missing piece already exists and just needs naming. No hint means
there is real work: a lemma, or an induction.

**Symmetric-looking statements are not symmetric.** How a definition
recurses decides which facts are free and which cost you an induction.
That asymmetry never goes away, and picking the convenient direction
when you have the choice is a genuine skill
([Proof recipes](#recipes)).

**You can always ask.** Between hovering a `⋆`, reading an obligation
and declaring a lemma you have not proved yet, there is never a reason
to sit and stare at a proof wondering what the checker wants.

## Where to go next

You now have the whole loop. From here:

- **Part II** is the language you were writing without being told:
  notation, definitions, operators, modules.
- Impatient about the proofs specifically? [Reflection](#reflection)
  explains what `⋆` really asks for, and
  [Proving by induction](#induction-proofs) explains `ℕ-elim`
  properly.
