# Introduction

Nova is a mechanised type theory: one language in which you write
programs, state theorems and prove them, and a checker that either
accepts your file or hands back the list of equations it could not
derive.

This book is about the **surface language** — the text you put in a
`.nova` file. The theory underneath it is specified in
`docs/NovaFoundation.txt` and rendered on the
[theory specs](specs.html) page. Where this book and a spec disagree,
the spec is right.

## A first taste

```nova
infixl 6 +
def + : ℕ → ℕ → ℕ ≔ λx. λy. ℕ-elim x (n ih. S ih) y

def plusZeroId : (n : ℕ) → n + Z ≡ n using (nat.+.eq) ≔ λn. ⋆

def zeroPlusId : (n : ℕ) → Z + n ≡ n using (+.eq, nat.plusZeroId) ≔ λn. ℕ-elim ⋆ (k ih. ⋆) n
```

That is the opening of `src/nova/nat.nova`, and nearly everything
characteristic about Nova is already on display:

- `+` is not notation for a function. `+` **is** the function's name;
  `infixl 6 +` only says how to parse it. Operators are names, so the
  obligation printer prints the name and the name is the operator
  ([Operators and fixity](#operators)).
- A theorem is a `def`. Its type is the statement, its definiens is the
  proof, and nothing distinguishes it from a program.
- Both proofs are `⋆`. `⋆` is *the* proof of every proposition,
  equations included — there is no `refl` and nothing to match on.
- `plusZeroId` holds by computation: `+` recurses on its **second**
  argument, so once `+` is allowed to unfold, `n + Z` already *is* `n`.
  `zeroPlusId` does not compute away, and so it inducts — but each case
  is still `⋆`, because in the step case the induction hypothesis is in
  scope and that is enough.
- `using (…)` names what this item's checking may use — here, the
  permission to unfold `+` at all (`+.eq`), and one earlier lemma.
  Definitions are opaque by default; nothing else in the file is
  visible to the checker unless it is named. It is not an import and
  not a hint; it is the item's **discharge scope**
  ([The discharge engine](#discharge)).

## Your program is checked twice

```text
  .nova source
      │  parse + scope resolution        (pure front end)
      ▼
  indexed surface AST
      │  ELABORATOR                      (untrusted)
      │    bidirectional pass; at every conversion site it consults
      │    the DISCHARGE ENGINE and records what it invents
      ▼
  annotated tree                         (the certificate-carrying artifact)
      │  KERNEL                          (trusted, total)
      │    synthesis + fuel-bounded beta + certificate replay
      ▼
  accept / reject
```

Everything above the kernel is untrusted. The elaborator may be
arbitrarily clever and the discharge engine may search, rewrite and
match heuristically; none of it is believed. The kernel re-establishes
every judgement from its own signature, replaying each recorded
conversion step mechanically.

Three consequences you can rely on as a user:

- A bug in the elaborator or the engine is **incompleteness** — a proof
  that should go through does not — never unsoundness. A bad step dies
  at replay.
- The kernel is **total**: it never diverges, because its normalisation
  is fuel-bounded and exhaustion means reject. Every artifact gets a
  verdict.
- The verdict is the kernel's; the *report* you read while working is
  the elaborator's.

## Equality is a proposition, and it reflects

`a ≡ b ∈ A` is an element of `Ω`, the universe of mere propositions —
not a type former, and not an inductive family. You nonetheless write
it exactly where a type goes, because a proposition **is** its type of
proofs: there is no wrapper to apply and none to strip. Propositions
are proof-irrelevant, so that type has one inhabitant, and its
canonical form is `⋆`.

The rule that changes everything is **reflection**: from a proof of
`a ≡ b ∈ A` you may conclude that `a` and `b` are *judgementally*
equal. Wherever the hypothesis is in scope, the checker may silently
replace one side by the other. So the usual equality toolkit is not a
library of clever inductions — it is a list of one-liners:

```nova
def sym : {A : 𝕌} (a b : A) → (a ≡ b) → b ≡ a ≔ λA. λa. λb. λh. ⋆

def cong : {A : 𝕌} (B : A → 𝕌) (f : (v : A) → B v) {v w : A} → (v ≡ w) → f v ≡ f w ≔
  λA. λB. λf. λv. λw. λh. ⋆

def transport : {A : 𝕌} (P : A → 𝕌) {a b : A} → (a ≡ b) → P a → P b ≔ λA. λP. λa. λb. λh. λp. p
```

`transport` is literally the identity function: with `a ≐ b` reflected
from the hypothesis, `P a` and `P b` are the same type, so the element
crosses unchanged. Function extensionality and UIP are theorems in the
same style. [Equality](#equality) tells the whole story.

The consequence that changes how dependently typed code *feels* is
that the repairing casts disappear from your types along with them:
vector append can be proved associative with no cast in the statement
and no coherence lemma in the proof
([Types without coherence](#coherence)).

The price is that type checking is undecidable. Nova's answer to that
is not a search budget and not a heuristic that sometimes lies.

## Obligations, not failure

When the conversion checker cannot derive an equation it needs, it does
not stop and it does not guess. It **assumes** the equation, records it,
and carries on. At the end of the run you get the list:

```report
defined scopedItemBad [+1 obligation]
open obligations (1):
  [1] (a : ℕ) (b : ℕ) ⊢ a + b ≐ b + a : ℕ
      at: def scopedItemBad: checking ⋆
      hint: closes with scopedItem
```

A file is accepted exactly when that list is empty — the run prints
`Accepted.` and nothing else is a pass. An obligation is neither an
error nor a proof: it is the checker telling you, in full and in your
own syntax, which equation it had to take on faith and where.

Note the `≐`: the report speaks in judgemental equality, while your
source states propositions with `≡`. And note the remedy, which is
mechanical — write the statement as a `def` above the failing item,
prove it, and name it in that item's `using` clause. [Reading the report](#report) goes
through it line by line.

Because every fact an item leans on is named at the item, an accepted
file is a self-contained record of *why* it is accepted.

## What Nova does not have

- **No tactic language.** There is no proof script layer, no `rewrite`
  pragma, no `auto`. You write definitions; the engine reuses the
  equations you have already proved.
- **No `refl`, no `J`, no matching on proofs.** Equality carries no
  data, so there is nothing to case-split on.
- **No general recursion and no termination checker.** Recursion is by
  eliminator, or by the clausal fragment ([Defining equations](#clausal-defs)) that compiles to
  one; corecursion is `corec` ([Coinductive types](#coinduction)).
- **No universe hierarchy.** Two universes are writable — `𝕌` for small
  types and `Ω` for propositions — with no levels and no arithmetic.
- **No type classes and no instance search.** Structures are ordinary
  Σ-codes passed by hand ([Pairs and Σ-types](#pairs)).
- **One form of user-defined type**: the `data` item, a quotient
  inductive-inductive signature ([The `data` item](#data)), which subsumes ordinary
  inductive families, indexed families, and quotients with
  constructors.

## How to read this book

- Part I is a tutorial; read it in order.
- Parts II–V are the reference proper, one language feature per
  chapter.
- Part VI is about *proving*: the discharge engine, the report, and the
  habits that make proofs go through. If you are stuck rather than
  curious, start at [The discharge engine](#discharge).
- Part VII is lookup material: grammar, precedence, notation, generated
  names, the library, tooling, glossary.

## Conventions used here

- Every code block is real surface syntax, highlighted with the same
  token classes the LSP sends an editor — the same colouring you see in
  the [rendered corpus](nova/index.html).
- Names in `code font` that look like `el-reflect` or `e-ty-eq` are
  rule names; you can find them on the [specs page](specs.html).
- Corpus citations name a file in `src/nova`. Most examples in this
  book are lifted from there, which means they are examples that
  actually check.
