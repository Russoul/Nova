# The discharge engine

Every non-trivial Nova proof is really a conversation with one
component: the conversion checker and the discharge engine behind it.
This chapter is the mental model. Get it right and the rest of proving
in Nova is bookkeeping; get it wrong and the reports look arbitrary.

## Conversion sites

Elaboration is bidirectional, and wherever a checked term meets an
expected type — or an inferred type meets an expected one — the
elaborator emits an **equation** and asks: are these two things equal?

The obvious site is a `⋆` at an equality proposition: the whole point
of writing `⋆` is to ask for `a ≐ b`. But the same question is asked
silently at every *switch* from inference to checking, so a mismatch
you never wrote down can still surface as an obligation. The report's
`at:` line tells you which kind of site you are looking at.

## The ladder

The checker tries the cheap things first and only ever assumes as a
last resort. In outline, from cheapest to most expensive:

1. **Identical as written** — discharged by reflexivity, with no
   normalisation and no candidate assembly. In a long explicit proof
   this is the majority of switches, which is why the explicit style is
   affordable.
2. **Computational join** — both sides normalised by every computation
   rule *except* signature unfolding, then compared. Definitions stay
   closed, so there is no unfolding blow-up. This is the strict sense of
   "trivial by computation": no store, no hypotheses, no loss of
   abstraction.
3. **Weak head normalisation**, now including signature unfolding — β
   plus opening definitions. Definitions are **opaque by default**: a
   definition opens here only if the site licensed it, with `<def>.eq`
   (its defining equation) or the weaker `<def>.unfold` (head exposure
   only). This is why `nat.plusZeroId` cites `+.eq` to prove something
   that is otherwise true by pure computation.
4. **Decomposition** — same rigid head on both sides, so compare the
   components and feed each back in. For the type formers and the
   universe codes this is *faithful*, not merely sufficient: downward it
   is congruence, upward it is injectivity. Two cases are only
   sufficient — `class` equations decomposed to representatives
   (quotients are not injective) and neutral-spine congruence.
5. **Proof discharge** — an element equation at `𝟙`, `𝟘` or at a
   **proposition** is closed outright, because proofs of a proposition
   are all equal. This is why an eliminator's coherence obligations
   vanish at a prop-valued motive, and why `<Sort>ElimP` takes no
   coherence arguments at all.
6. **η** — comparison at a Π always moves under the binder, so two
   neutral functions can be joined pointwise by a Π-wrapped hypothesis.
   This is where function extensionality comes from. Pairs compare by
   projections, and same-tag injections by their payloads.
7. **The store** — the three mechanisms below.
8. **Assume** — record the equation as an obligation and continue.

A rigid head **mismatch** is an obligation, not an error. No-confusion
is a property of consistent contexts, not a rule, and you may be
working under a hypothesis that has made the context inconsistent on
purpose.

## The scope: what the engine is allowed to use

This is the single most misunderstood part of the system, so it is
worth stating flatly.

> The store is not a search space. A site consults only its **scope**:
> the lemmas the enclosing item **names** in its `using` clause, plus
> the **hypotheses** of the context, which are always in scope. The
> same clause carries the unfold licences (`<def>.eq`, `<def>.unfold`),
> the rewrite licences (`<lemma>.rw`, `hyp.rw`) and the η builtins
> (`pi.eta`, `sigma.eta`).

An item with no `using` clause scopes to hypotheses alone. A lemma
sitting above your item, accepted and correct, does *nothing* for it
unless it is named, applied explicitly, or is a hypothesis.

Three consequences follow, and they are the reason the design is this
way:

- Whether an item is accepted is a function of **the item**, not of the
  store or its order.
- The per-conversion cost is proportional to the named set, not to the
  size of the library.
- A lemma that would fire spuriously is never even tried.

Order still matters, but only in two specific senses: a name in `using`
must resolve to something already elaborated, so the lemma has to sit
*above* the item; and a candidate's sides are stored normalised as of
its acceptance point, so a lemma stated in one spelling still matches
goals that earlier rules have canonicalised.

Hypotheses being automatic is what makes induction proofs look magical.
In the step case of an `ℕ-elim` at an equality motive, `ih` is an
equality-typed binder, so it is reflected into the scope, and `⋆`
closes the case with no citation.

## The three store mechanisms

Within the scope, a candidate can fire in three complementary ways.

**Whole-equation match.** The goal, or its flip, matches a candidate's
two sides under one consistent first-order instantiation. Parameters
the sides do not determine must carry a prop — equality props
included — or a `𝟙` type, and their instances are discharged as side
conditions — which is how
hypothesis-conditional lemmas (well-definedness facts, order-respecting
laws) fire. Matching treats a code in type position as an ordinary
pattern position, so a lemma stated generically discharges its
instantiated goals: prove it once at `(a : 𝕌)` and every `ℕ` instance
follows.

**Rewriting**, and only when licensed. Equations usable as terminating
rules — strictly size-decreasing ones first, then size-preserving
non-permutative ones — are applied left to right at any subterm, to a
bounded fixpoint, before comparison. A plain citation does **not** turn
a lemma into a rewrite rule; the site must ask, with `hyp.rw` or
`<lemma>.rw`. Reach for it when the redex sits under a different head,
where decomposition cannot descend.

**Transitivity hops.** A candidate that rewriting cannot apply may
rewrite one side wholesale, recursing within a small depth budget —
chaining, say, an exchange law, a hypothesis, and an exchange law
again.

## What never fires

Two shapes are excluded from rewriting by construction, and knowing
them saves hours:

- **Permutative equations** — sides equal up to a bijective renaming of
  the parameters: commutativity, exchange laws. As rewrite rules they
  would oscillate forever. They remain available to whole-equation
  match and to hops, where the full statement pins the instantiation —
  so state the exact shape you need, e.g. `a + (b + c) ≡ b + (a + c)`
  rather than hoping commutativity will find it.
- **Equations whose left side has no rigid head** — a bare parameter
  spine like `v` or `v .π₁`. First-order matching is type-blind, so
  such a rule would fire at ill-typed positions and its certificate
  would die at replay, taking the discharge with it.

And one shape can never be used at all: a lemma with a parameter
occurring in **neither** side. A candidate carries no type slot, so
nothing can bind that parameter — the lemma is unusable and its goal
comes back verbatim, unhinted.

## Assume, and the hint

If nothing closes the equation, the engine appends it to the signature
as a machine-named hole, records where it came from, and succeeds.

Just before assuming, it probes the **whole** store once — the same
mechanisms, unscoped, plus a kernel replay of the result — and records
what *would* have closed the equation as an advisory `hint:`. Search is
demoted to feedback, never to acceptance. The upshot is that the remedy
the report prints is usually literal: add the hinted name to the
surfacing item's `using` clause. Two shapes of hint appear —

```text
hint: closes with plusComm                -- name that lemma
hint: closes by citing nat.+.eq           -- license that unfolding
```

— and they are exactly the two ways a site's scope can be too small.

Deduplication is by statement, so one equation appears once no matter
how many sites hit it. Within a run, an equation matching an
already-assumed obligation is deduplicated against it, **not**
discharged by it: assumptions can never launder themselves into
proofs. The wall between assumed and proven is crossed only by the
prepend-and-rerun cycle.

## A worked example

From the test suite. `plusComm` is proved and accepted, and then two
items ask for the same thing:

```nova
def scopedItem : (a : ℕ) (b : ℕ) → a + b ≡ b + a ∈ ℕ using (plusComm) ≔
  λa. λb. ⋆

def scopedItemBad : (a : ℕ) (b : ℕ) → a + b ≡ b + a ∈ ℕ using (plusZeroId) ≔
  λa. λb. ⋆
```

The first is accepted: `plusComm` is in scope, whole-equation match
finds the instantiation, done. The second is not:

```report
defined scopedItem
defined scopedItemBad [+1 obligation]
open obligations (1):
  [1] (a : ℕ) (b : ℕ) ⊢ a + b ≐ b + a : ℕ
      at: def scopedItemBad: checking ⋆
      hint: closes with scopedItem
```

Same store, same file, same goal — different `using` clause, different
verdict. That is the scope discipline doing exactly what it promises,
and the hint pointing at the fix.

## How this shapes the way you write

- **State the shape you need.** Matching is first-order, so a
  permutative fact has to be stated at the instance you want.
- **Prefer generic lemmas.** They are matched up to instantiation, so
  one type-generic statement discharges a whole family of goals.
- **Name deliberately, one at a time.** Licences are not monotone —
  citing more can *undo* a proof by unfolding the goal into a
  vocabulary your stored lemmas no longer match. [`using`: licences and scope](#using-clauses) has the symptom and
  the discipline.
- **Reach for `.rw` only when descent cannot reach.** It is the
  expensive mechanism and the one that changes the goal's shape under
  you.

## Why none of this can go wrong

The engine is untrusted. Every discharge it performs is recorded as a
certificate and replayed by the kernel, step by step, at the exact
position it claims. A wrong guess is a failed replay, never a wrong
acceptance — so the engine's cleverness is a quality property, and only
the kernel's correctness is a safety property.
