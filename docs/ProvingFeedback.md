# Proving in Nova — accumulated feedback

A running log of friction encountered while *using* Nova to develop
mathematics, as opposed to specifying it. Not a spec: nothing here is
normative, and several items are consequences of deliberate design
choices rather than defects. Each entry records what happened, where,
what it cost, and — where there is one — a suggested fix.

Sources so far: the ℤ → Rat → ℚ development
(`integer.nova`, `integerAdd.nova`, `integerMul.nova`, `rational.nova`,
`rationalQ.nova`, `rationalInv.nova`), the observational
equality/disequality of ℤ (`eqInt.nova`), and the constructive reals
(`ratBound.nova`, `ratHalf.nova`, `ratArch.nova`, `realNeg.nova`,
`realAdd.nova`, `realEq.nova`, `realOrder.nova`) — items tagged **[ℝ]**
below come from the last of these.

---

## A. Design constraints that shape developments

These follow from the theory as specified. They are not bugs, but they
determine what a development can look like, and they cost real time
when discovered mid-way.

### A-1. No 𝕌-code for `Prf` / `Ω`

The natural definition of a subtype — carry the property as a proof
component — cannot be a code:

```
type Rat ≔ (n : El Int) ⨯ (d : El Int) ⨯ Prf (¬ (d ≡ intZero ∈ El Int))
```

is a *large* type: no `El Rat`, no generic `(A : 𝕌)` combinators from
`equality.nova`, no use as a code anywhere. `ty-sigma`/`ty-quot` accept
arbitrary types, so quotienting still works, but the loss of code-hood
is severe enough that the whole ℚ development instead carries
non-zeroness **structurally** (`NZ ≔ ℕ ⊎ ℕ`, denoting ±(n+1)).

### A-2. Realizer irrelevance forbids dispatching on a proof

Even with a large proof-carrying type, a *function* cannot use the
proof: proofs are irrelevant, so `qInv : (u : El Q) → Prf (u ≢ 0) →
El Q` cannot inspect the witness to build an inverse. Reciprocals
therefore needed a second structural code, `NZQ ≔ NZ ⨯ NZ`, with a
total inversion (the swap) and an embedding into ℚ. The resulting
field statement is honest but non-classical in shape.

Worth stating in the docs explicitly: *any* "partial operation defined
where a property holds" must be re-expressed as a total operation on a
type whose elements structurally satisfy the property.

### A-3. Quotients are not effective — RESOLVED upstream

*Was:* nothing inverts `el-quot-eq`, so from `class p ≡ class q` one
could not recover `Prf (R p q)`, and disequalities in a quotient type
were unavailable.

*Now:* `quotEffective.nova` shows class equality **is** the equivalence
closure `r⁺` (`classEqIff`), with effectivity on the nose at an
equivalence (`effectiveAtEquiv`), and `intEffective.nova` instantiates
it for ℤ. A disequality is now three lines — refute the relation and
compose (`intNonZero.nova`'s `intNeqOfNotRel`).

Downstream, `rationalEffective.nova` instantiates the same corollary at
ℚ. The one premise `effectiveAtEquiv` asks for — that the relation be
an equivalence — is where the earlier work paid off: transitivity of
cross-multiplication is cancellation by a non-zero integer, i.e.
`intNoZeroDiv`. Effectivity then delivers the converse that had been
out of reach (`qOfNzqNonZero`, `qInvertibleIffNonZero`).

What this does **not** give, and the distinction is worth keeping:
effectivity is PROPOSITIONAL. It hands back `Prf (r p q)`, never a
decision. Anything that has to branch on zero-ness still needs a
canonical form computed as data (D-4), which is why `intCanon` and its
`normPairWD` survive unchanged.

### A-4. `code-prop-eq` is not usable — RESOLVED upstream

*Was:* the rule was judgemental but had no term form, and the automatic
check fired only on the evident (`𝟙`-shaped / reflexive-`≡`-shaped)
cases — so the natural way to define an observational relation on a
quotient, `quot-elim` landing in `Ω`, was blocked on its
well-definedness.

*Now:* exactly the suggested fix landed — supplied witnesses
(`e-star-propext`), surfaced as

```
propExt : (p : Ω) (q : Ω) → (Prf p → Prf q) → (Prf q → Prf p) → p ≡ q ∈ Ω
propExtOfIff : (p : Ω) (q : Ω) → Prf (p ↔ q) → p ≡ q ∈ Ω
```

and the companion `e-star-quot-wit` for class equations, which makes
`classEqOfRel` generic in the relation (`⋆ h`, no shape restriction, `r`
may be a variable). `quotEffective.nova`'s `clsRelWd` is the first real
use: an Ω-equation between two closure instances, discharged by
`propExt` from the closure's own transitivity and symmetry.

### A-5. Squash elimination stops at propositions, and cannot be widened for free

`el-squash-e-prf` lands in `Prf q` (its conclusion is literally `⋆`);
there is deliberately no eliminator into arbitrary types. The obvious
refinement — *allow it into any type C that is a subsingleton* — is
the standard rule elsewhere (HoTT's truncation recursion into props,
Lean's `Squash.lift`), and Foundation's own stated objection does not
rule it out: "el-prf-prop would force it constant" is harmless exactly
when C has at most one element. The model justification also carries
over verbatim — "validated by instantiating their premise at any
carrier element; the conclusion never consults which one" is precisely
what a subsingleton C licenses.

What blocks it is the *forced* realizer irrelevance: `Prf p`'s one
canonical form is `⋆`, so **there is no Prf-beta** (Foundation says so
outright). An eliminator into a data-carrying C could therefore never
reduce: a closed term of a Σ-type would be stuck, never a pair. The
rule would buy derivations, not algorithms.

Concretely, in this development: `(v : El Q) ⨯ Prf (qMul u v ≡ qOne)`
IS a subsingleton (inverses are unique — `qInvUniqueVal`,
`qInvWitnessUnique` in `rationalAlgInv.nova`), so the rule would have
derived the non-erased inverse straight from the squashed one, deleting
`intCanon`'s data-valued view and the no-zero-divisor argument (~250
lines). But the inverse so obtained would not compute: `qInv (qcls
third) ≡ qcls 3` holds by `⋆` today and would not then. The two are
genuinely different results.

### A-6. Equality combinators are 𝕌-indexed, so large types have none

`trans`, `sym`, `cong`, `transport` all take `(A : 𝕌)`. A type carrying
a `Prf` — such as the inverse Σ above — is not a code, so **none of
them apply**, and `trans (…) …` at such a type is not even a parse.
Every development that touches a large type must re-declare its own
transitivity, symmetry and η, monomorphically, spelling the type out
at each occurrence.

Worse, the code-generic `pairEta : (A B : 𝕌) …` misfires there: the
engine matches it against a large-Σ η goal, instantiates `A`/`B` with
non-codes, and the kernel rejects the certificate — B-3 again, one
level up. That is why `qInvIsProp` is stated in pair-congruence form
(`invPairCong`, both sides literal pairs, no η) rather than as
`w ≡ w'`.

**Suggested fix:** a second set of combinators quantified over *types*
rather than codes, or admissible congruence/η at arbitrary types.

### A-7. [ℝ] A Σ-CODE's proof component is data — a feature, and (once UIP landed) not a cost

A Bishop real is a pair `(f , reg)`: a sequence and a witness that it
is regular. By A-1 a Σ-code cannot carry a `Prf`, so `Regular f` is a
𝕌-code (a Π of a pair of `LeQ`s) and `reg` is DATA. Three separate
things follow, and an earlier version of this entry ran them together.

**1. It is what makes ℝ a code at all.** `Regular f : 𝕌` is what makes
`RSeq : 𝕌`, hence `Real : 𝕌`, hence `El Real`, hence every generic
`(A : 𝕌)` combinator in `equality.nova` applicable to reals. Had the
witness been a `Prf`, the entire ℝ development would have been large
(A-6) and would have had to re-declare its own `trans`/`sym`/`cong`.
This is A-1's trade paying off, not costing.

**2. Here the witness carries no rate — the rate is in the TYPE.**
It is tempting to read `reg` as the modulus of convergence, and in a
Cauchy-with-modulus carrier

```
((f : ℕ → Q) ⨯ (μ : ℕ → ℕ) ⨯ ⟨∀ε ∀m n ≥ μ ε. |f m − f n| ≤ ε⟩)
```

it would be exactly that: `μ` is load-bearing data, you cannot compute
with the sequence without it, and *there* the fact that a Σ-code cannot
erase it is precisely what you want. But `real.nova` uses Bishop's
REGULAR sequences, whose whole design is to move the modulus into the
type:

```
def Regular : El (ℕ → Q) → 𝕌 ≔
  λf. ((m : ℕ) (n : ℕ) → (LeQ (qNeg (rBound m n)) (f m − f n)
                          ⨯ LeQ (f m − f n) (rBound m n)))
```

`rBound m n` is a fixed function of the indices. Every element of
`RSeq` therefore converges at the SAME rate, by definition, and two
witnesses for the same `f` certify literally the same inequalities.
What `reg` actually contains is, per index pair, the sign VERDICT —
which injection of `NonNegS s ≜ Id Sign s sZero ⊎ Id Sign s sPos` —
and that is determined by `f`, since `sgnQ` is a function and
`sZeroNotPos` rules out both branches being inhabited at once. So the
witness has at most one shape; it is a subsingleton in everything but
name.

Consistent with that, no proof in the ℝ development ever inspects a
regularity witness: `regBnd` passes the pair along and the `Bnd`
algebra consumes `.π₁`/`.π₂` as opaque verdicts.

**3. The missing UIP — RESOLVED upstream.**

*Was:* "subsingleton in everything but name" was the problem. To prove
two `RSeq` elements with the same sequence equal one needs `Id a x y`
to be a subsingleton, and I could not derive it. Two routes, both
blocked structurally:

* induction on `p : El (Id a x y)` with motive `λu v w. (w ≡ refl a u ∈ …)`
  does not typecheck — `refl a u : El (Id a u u)` and the motive needs
  it at `El (Id a u v)`, with `u ≐ v` unavailable at generic indices;
* the "for every `z`" motive has to be an Ω, and Ω is not closed under
  `→` (`prop.nova` squashes: `p ⊃ q ≜ ∥Prf p → Prf q∥`), so the motive
  becomes `∥(z : El (Id a u v)) → Prf (w ≡ z)∥` and its `refl` method is
  the original goal again.

So every law about ℝ had to route through the quotient relation REq;
carrier equality was unavailable.

*Now:* `uip.nova` derives it, and the move is precisely the one both
routes above were missing — carry the index equation as a BINDER of a
squashed Π inside the motive,

```
λu. λv. λw. ∥(k : u ≡ v ∈ El a) → (w ≡ refl a u ∈ El (Id a u v))∥
```

so that `k` is in scope, and reflected, exactly while the codomain is
typed. That makes `refl a u` well-typed at `El (Id a u v)` and the
`refl` method becomes `⋆ (λk. ⋆)`. (In intensional MLTT J cannot prove
UIP — Hofmann–Streicher; here reflection is what pays.)

Downstream, `realSeq.nova` cashes it in three steps —
`nonNegIsProp` → `bndIsProp` (both in `ratBound.nova`) →
`regularIsProp` by dependent funext twice → `rseqEq` — and `RSeq`
becomes a set whose equality is equality of the underlying sequence.

What that bought, concretely: a binary operation on ℝ owes TWO
well-definedness proofs, and `rationalQ.nova` gets the outer one free
for `qAdd` by commuting (`ratAddComm` is an equation in `Rat`, a plain
Σ-code). One level up that move was unavailable, so `realAdd`,
`realMax` and `realMin` each carried a transcription of their inner
proof with the arguments swapped. With `rseqEq` the commutativity of
each operation is provable ON REPRESENTATIVES, and the outer case
collapses to one line through a combinator generic in the operation
(`wdOuterOfComm`) — about 50 lines of duplicated bound arithmetic
deleted. The pointwise laws (`realAddOfQ`, `realAbsNeg`, …) also stop
routing through closeness: they are equalities of representatives and
now say so.

One wrinkle worth recording, because it is B-1 again: `rseqEq` cannot
simply read `y`'s witness at `Regular (seqOf x)`. The conversion
`Regular (seqOf y) ≐ Regular (seqOf x)` under a reflected sequence
equation is one the engine finds and the kernel refuses — the rewrite
lands inside `qAdd`, i.e. inside a `quot-elim` scrutinee. Even with
both sequences as bare variables it fails. `transport` moves the
witness instead: it is the identity function, so nothing is inserted,
but its SIGNATURE does the retyping, and the conversion is never
demanded at the call site because it was discharged once, at an
abstract motive (D-3).

---

### A-8. [ℝ] Two witnesses, because two operations want different things

ℝ ends up with two data-carrying hypotheses, both bracketed, and the
difference is not bookkeeping:

```
PosR x     ≜ Br ((p : RSeq) ⨯ (k : ℕ) ⨯ prfC (x ≥ 1/(k+1)) ⨯ Id Real (class p) x)
NonNegR x  ≜ Br ((p : RSeq) ⨯ ((n : ℕ) → LeQ qZero (seqOf p n)) ⨯ Id Real (class p) x)
```

`PosR` carries a MODULUS — a rate of separation from zero. `NonNegR`
carries a NONNEGATIVE PRESENTATION — a representative that is
pointwise ≥ 0. Which one an operation needs is decided by its
domain, and it is easy to reach for the wrong one:

* **0 has no modulus, and that is not an accident.** `qInvNat k` is
  strictly positive for every k, so `PosR realZero` is uninhabited —
  not unproved, uninhabited. A modulus answers "how far from 0 is x,
  at worst?", and 0 is not separated from itself. Any operation whose
  domain is CLOSED at 0 cannot use PosR.
* **√ never needed a modulus.** It needs its SAMPLES nonnegative.
  Strict positivity is one way to arrange that — deepen the sample by
  the modulus until p_j ≥ 1/(2(k+1)) — but a nonnegative presentation
  says it directly, covers 0, and is simpler: the deepening
  disappears, and with it five supporting lemmas.
* **Division will need PosR**, because 1/x genuinely requires
  separation: the modulus is what says how deep to sample before the
  reciprocal is defined at all. There 0 is correctly outside the
  domain, so nothing is lost.

The clamp survives in exactly one place — `nonNegMk`, which builds a
NonNegR witness from `x ≥ 0` and any representative by taking
max(·, 0). That is the honest content of "a nonnegative real has a
nonnegative presentation", and it is a theorem, not a definition
buried inside √.

## B. Engine / kernel mismatches

The dominant time sink. In all of these the discharge engine finds a
derivation and the *kernel* refuses the certificate, so the error
arrives late, phrased in core terms, with no source-level pointer to
the offending step.

### B-1. Rewrites may not land in a stuck eliminator's scrutinee

`NovaKernel.txt` §6: at a type-undetermined rewrite point the subterm
must be `⇒ᴺ`-inferable. A stuck `⊎-elim` or `quot-elim` is not. Since
`intAdd x y` unfolds to `quot-elim … x`, **both arguments of `intAdd`
are scrutinee positions**, so no rewrite may land in either unless the
subterm happens to be a variable-headed spine.

Diagnostic: `replay failed: kernel: step at a type-undetermined
position`.

Seen in: `intScaleNZero` (first attempt), `ratAddZeroLNum`,
`intAddScaleZeroL`, `ratAddZeroL/R`.

Workarounds that work:

* generalise the argument that would be rewritten to a **variable**, so
  there is nothing to rewrite there (`intAddScaleZeroL (d) (y)`);
* do the `⊎-elim`/`quot-elim` case split *earlier*, so the branch goal
  closes at the **root** (a type-determined position);
* stop relying on the engine and compose with explicit `trans` — a
  lemma application is unconstrained by position.

**Suggested fix:** make the engine kernel-aware so it never emits a
certificate the kernel will reject (and can instead search for a
different route); failing that, report the source position and the
offending subterm rather than the raw core step.

### B-2. Σ-η does not contract in kernel normal forms

`el-sigma-eta` is judgemental in the theory, but replay does not
contract `(t .π₁ , t .π₂)` to `t`, so every chain ending at a pair
needs a **named** η hop. Each of these is `⋆` on its own; it just
cannot be left implicit.

Seen in: `ratEta`, `pairEta`, `classPairEta`, `pairEq2`, and again in
`qNegNeg`. Typical rejection: `types differ after replay` with the two
sides differing only by `(q.π₁, q.π₂)` vs `q`.

**Suggested fix:** η-contract pairs during normalisation.

### B-3. Lemma matching is first-order and type-blind

A `ℕ ⨯ ℕ`-specific

```
def pairEta : (p : ℕ ⨯ ℕ) → (p .π₁ , p .π₂) ≡ p ∈ El (ℕ ⨯ ℕ)
```

fired at a pair of type `El Rat`; the kernel then rejected the
certificate (`proof argument type mismatch`). Worse, the failure was
**non-local**: `rational.nova` was `Accepted.` standalone and failed
only when imported into a module that also imported the offending
lemma.

Rule of thumb learned: *state η/congruence-shaped lemmas generically*
(`(A : 𝕌) (B : 𝕌) (p : El (A ⨯ B)) → …`), because a lemma will be tried
anywhere its shape matches, regardless of type.

**Suggested fix:** check the candidate's type at the match position
before using it (the kernel already does; the engine should too).

*Recurred* with a **conditional** lemma: `eqInt.nova`'s
`pairEq2 : (x y : ℕ ⨯ ℕ) → x.π₁ ≡ y.π₁ → x.π₂ ≡ y.π₂ → x ≡ y`, whose
conclusion is two variables, matched at `El Rat` (its side conditions
being discharged there by β/η) and again broke an importing module.
Generalising it over `(A B : 𝕌)` fixed it. So the rule is not just
about η lemmas: **any lemma whose conclusion is shape-generic must be
type-generic too.**

### B-4. Assumed obligations are usable facts, and silently poison proofs

An item with open obligations still enters the store with those
obligations *assumed*. Downstream items — including items in modules
that merely import the failing one — can then be "proved" from
absurdities such as `c .π₁ ≐ c .π₂`.

Concretely: a probe of the `intMul` associativity identity passed in a
scratch file and failed once the file it belonged to was fixed. The
scratch file had imported a module whose `intMulComm`/`intMulAssoc`
were still failing, and their assumed obligations (`a .π₂ ≐ a .π₁`,
…) made the probe vacuous.

Practical rule: **only a module that reports `Accepted.` is evidence**;
a green-looking item in a file with open obligations elsewhere is not.

**Suggested fix:** taint items whose derivation used an assumption, and
report them separately from genuinely closed ones; consider not adding
assumed equations to the candidate store at all.

### B-5. Context sensitivity of proofs — RESOLVED by scoped discharge

*Was:* following from B-3/B-4: whether a `⋆` closes depends on the full
candidate store, which depends on imports, on item order within the
file, and on whether *other* items failed. Proofs are therefore not
stable under refactoring — moving a lemma, or adding an unrelated
import, can break a proof several items later.

*Now:* discharge is SCOPED (docs/SearchlessElaboration.md §5.3, the
default semantics of NovaElaboration.txt): an item sees only the
lemmas its `using` clause names, plus hypotheses — so whether it
closes is a function of the item. B-3's misfires are never tried
unless named (and the kernel gate still rejects them when they are);
the store's only residual order-sensitivity is the normalized form of
stored candidate SIDES. The whole-store search survives as the
report's `hint:` line, which usually names the exact clause edit.

---

### B-6. Conversion at a class-equation type goes through the relation

Checking a type against **itself** can fail. The report shows

```
from composite: ⊢ class (c .π₁ , c .π₂) ≡ z ∈ El Int
              ≐ class (c .π₁ , c .π₂) ≡ z ∈ El Int  type
```

with an obligation `c .π₁ ≐ c .π₂` underneath. Cause: `class` is an
intro form, so `class a ≐ class b` is decided via the quotient
*relation* rather than structurally — even when `a` and `b` are the
same term. The relation instance here is `a.π₁ + a.π₂ ≡ a.π₂ + a.π₁`,
so the check needs `plusComm` **in scope** (it silently fails if the
importing module did not open it), and the resulting certificate
mentions the representative, which for `c ≔ intCanon z` is a
`quot-elim` spine and therefore not `⇒ᴺ`-inferable — so replay fails
with `proof element not inferable: QuotElim …`.

Seen in: `rationalInv.nova`, every attempt to state a lemma whose type
mentions `class (intCanon z .π₁ , intCanon z .π₂)`.

**Suggested fix:** a syntactic-identity fast path in conversion, before
any relation-based decision. Nothing should be provable-or-not about
`X ≐ X`.

### B-7. `¬ p` does not convert to `p ⊃ ⊥` reliably

`impIntro`/`impApply` are stated at `⊃`; a hypothesis of type
`Prf (¬ X)` should be usable directly since `¬ p ≜ p ⊃ ⊥`. For small
`X` it is. For large `X` the elaborator failed the conversion and
decomposed into nonsense obligations. Defining the two combinators
**at `¬`** —

```
def notIntro : (p : Ω) → (Prf p → Prf ⊥) → Prf (¬ p) ≔ λp. λf. ⋆ f
def notApply : (p : Ω) → Prf (¬ p) → Prf p → Prf ⊥ ≔
  λp. λh. λe. squash-elim h (g. g e)
```

— removes the conversion from every call site and fixed it. These
belong in `prop.nova`.

### B-8. Import ORDER decides whether a transitive import elaborates — RESOLVED upstream

`integerNormalize.nova`'s `intNormalize` — accepted everywhere else —
failed with `proof argument type mismatch` when a new module listed its
imports in a different order. Cause: modules are elaborated in first-
encounter order, so the store in which `integerNormalize` is checked
depends on which of its *siblings* came first. Here `rationalQ.nova`'s

```
clsEqOfRel : (p q : El Rat) → Prf (RatR p q) → class p ≡ class q ∈ El Q
```

had entered the store first; its conclusion is two variables, so
(B-3, type-blind matching) it fired on `intNormalize`'s well-definedness
goal `class (normPair …) ≐ class (normPair …)` at `El Int`, and the
kernel rejected the result.

Workaround: import the module that fixes the good order **first**
(`import intNonZero (…)` before everything else in
`rationalAlgInv.nova`).

This is the sharpest form of B-5: **a module's acceptance is not a
property of the module.** Anything downstream can break it, and the
error surfaces inside a file the author never touched.

*Now:* the lemma store is scoped to a module's import closure — each
module's lemmas are archived under its name and the visible store is
rebuilt on entry from the closure's archives. A module no longer sees
lemmas of modules it does not import, so acceptance IS a property of the
module again. The aggregate root `src/nova/all.nova` elaborates in
either alphabetical or topological order, which is the regression test
for it; `check-elaborations.sh` uses it by default.

### B-9. [ℝ] AC-shaped goals over a quotient carrier: derived, then rejected

The sharpest recurrence of B-1. Bounds in the reals are sums of unit
fractions, and a triangle-inequality chain produces them in whatever
association `bndVia` happened to build. Re-associating a six-leaf sum

```
((β + (β+β)) + (β+β)) + β  ≡  ((β+β) + (β+β)) + (β+β)     -- in ℚ
```

is *pure associativity* (both sides right-nest to the same term), and
`using (qAddAssoc, qAddComm, qLeftSwap, qPairSwap)` with `⋆` does find
a derivation — which the kernel then refuses:

```
replay failed: kernel: proof element not inferable: QuotElim (QuotElim (Class …
```

Cause as in B-1: `qAdd` is `quot-elim` on both arguments, twice over
(ℚ is a quotient of a Σ over a quotient), so *every* position inside a
ℚ-sum is a stuck scrutinee and no rewrite may land there. The size of
the dumped core term (~6 kB for one 8-leaf goal) also makes G-1 acute.

Workaround that works, and is worth stating as a technique: **never let
the chain choose the association.** Prove one *generic* rearrangement
lemma over variables, where every position is variable-headed —

```
qFourSum : (a b y : El Q) → ((a+b) + y) + (b+a) ≡ (a+a) + ((b+b) + y)
```

— and apply it by name (`bndEqB`) at each step. `qFourSum` is four
`cong`/`trans` links and elaborates instantly; the same identity
attempted in situ on the real bound does not go through at all. This
is D-3 (keep representatives abstract) applied to *operators* rather
than to elements.

**Suggested fix:** unchanged from C-2 — AC-normalisation would delete
this entire class of lemma. Failing that, the engine should not offer a
certificate whose steps sit inside a `quot-elim` scrutinee.

### B-10. [ℝ] `el-quot-eq`'s automatic route stops at equation relations

`class x ≐ class y` in `A / R` is discharged automatically only when
`R` is `∥𝟙∥`-shaped or an equality proposition (NovaElaboration's note
under `e-star-quot-wit`). The reals are quotiented by a *squashed*
closeness condition, so

```
def realEqOfREq : (x y : El RSeq) → Prf (REq x y) → class x ≡ class y ∈ El Real ≔
  λx. λy. λh. ⋆
```

reports a bare open obligation `class x ≐ class y : El Real`, with no
indication that the fix is to write the witness: `⋆ h`. Since the same
spelling *is* correct one module down (`clsEqOfRel` for ℚ, whose
relation is an equation), the failure reads as a soundness surprise
rather than as a missing argument.

**Suggested fix:** when a `class a ≐ class b` obligation is reported and
the goal's relation is not in the automatic fragment, say so and name
`⋆ e` in the hint line.

### B-11. [ℝ] A quot-elim whose method is not `⋆` owes an equation between PROOF TERMS

`quot-elim` at an ≡-typed motive still generates its own
well-definedness goal, and when the method is an explicit proof term
that goal is

```
normPairSum (p .π₁) (p .π₂)  ≐  normPairSum (p' .π₁) (p' .π₂)
    :  intAbs (intNeg (class p)) ≡ intAbs (class p) ∈ ℕ
```

— an equation between two *proofs* of the same proposition, i.e. an
instance of proof irrelevance. The engine does not reach for
irrelevance first; it looks for a derivation, finds one, and the kernel
rejects the certificate (`proof element not inferable: NatElim …`).

Worst of all, whether it does so is STORE-DEPENDENT: `intAbs.nova` was
`Accepted.` standalone and failed the moment it was elaborated inside
`src/nova/all.nova`. Naming `prop.irrel` in the `using` clause fixes it
in both.

Rule: **any `quot-elim` with a non-`⋆` method should list `prop.irrel`
in `using`.**

**Suggested fix:** try proof irrelevance FIRST at a `Prf`-typed goal,
before any search.

### B-12. [ℝ] Decomposition beats whole-equation match

The same lemma, applied by name, works; left to `⋆` it does not. Goal:

```
normPair b a .π₁ + normPair b a .π₂  ≐  normPair a b .π₁ + normPair a b .π₂
```

with `normPairSum` (exactly that equation, over variables) in the
`using` clause. The engine splits the sum congruentially into
`… .π₁ ≐ … .π₁` and `… .π₂ ≐ … .π₂` — both FALSE, since the two
components swap — and reports those. Whole-equation match never runs.

**Suggested fix:** try whole-equation match against the named
candidates before congruential decomposition, or at least fall back to
it when a decomposed branch fails.

### B-13. [ℝ] A calc chain can fail where the same proof by `trans` succeeds

`realNegUnique`, written as

```
(v ≡⟨ sym … (realNegPlusCancel u v) ⟩ realAdd (realNeg u) (realAdd u v) ≡⟨ … ⟩ …)
```

fails with `chain, step 1 [replay failed: kernel: step at a
type-undetermined position]`. The identical derivation written with two
nested `trans` is accepted. Cause: a chain link is a rewrite STEP, and
must land at a `⇒ᴺ`-inferable position (B-1); `realAdd` is a nested
`quot-elim`, so its arguments are not. `trans` is an ordinary lemma
application and is unconstrained by position.

The chain form is otherwise the single biggest readability win in the
corpus (E-2's suggested fix, delivered), so this is worth documenting
rather than avoiding: **when a chain step fails at replay, re-spell
that one step as `trans` before looking for a different lemma.**

### B-14. [ℝ] The lemma matcher cannot reach a metavariable inside a stuck quot-elim

The sharpest engine limit found so far, and the one that shaped a
module. A `using` candidate

```
qFloorWD : (p p' : El Rat) (h : Prf (RatR p p')) →
             divN (intAbs (num p)) (nzMag (den p))
           ≡ divN (intAbs (num p')) (nzMag (den p'))
```

does NOT fire against the goal it is literally the statement of —
`divN (intAbs (num p)) (nzMag (den p)) ≐ divN (intAbs (num p')) …`,
with `h` in context. Not a side-condition problem, and not
decomposition: the goal is reported whole and unchanged.

Bisected by probing the same descent with different methods (a
DECLARED lemma is enough to test matching without proving anything):

| method | fires? |
|---|---|
| `nzMag (den p)` | yes |
| `divN (nzMag (den p)) (nzMag (den p))` | yes |
| `divN (nzMag (den p) + nzMag (den p)) (nzMag (den p))` | yes |
| `intAbs (num p)` | **no** |
| `divN (intAbs (num p)) (nzMag (den p))` | **no** |

So compound arguments, `+`, and `divN`'s own huge fuel-recursive
normal form are all fine. What is not is `intAbs`, whose body is
`intCanon z .π₁ + intCanon z .π₂` — the metavariable ends up inside
`intCanon`'s `quot-elim` SCRUTINEE, and matching will not descend
there. (It is the matching-side twin of B-1, which says a rewrite may
not LAND there.)

Workaround, and it is a good one: compute the same natural without
`intCanon`. `intAbs.intMag` reads the magnitude straight off a
difference pair, `magPair r ≔ (r.π₁ ∸ r.π₂) + (r.π₂ ∸ r.π₁)`, whose
own descent is one monus lemma. With `intMag` in place of `intAbs` the
identical `using` clause fires on the first try. Both functions compute
the same natural; only one is visible to the engine.

**Suggested fix:** let matching descend into a stuck eliminator's
scrutinee. Nothing is unsound about it — the kernel's restriction is
about where a rewrite may be APPLIED, not about where a pattern may
look.

### B-15. [ℝ] A subsingleton lemma cannot discharge a descent into data

`quot-elim` into `El (LeQ x y)` owes `verdict ≐ verdict'`, and `LeQ` is
a subsingleton, so `leQIsProp : (x y : El Q) (p q : El (LeQ x y)) →
p ≡ q` ought to close it. It never fires, and this time the reason is
E-1's rule rather than B-14's: the index `x`/`y` appears ONLY in the
type, so first-order matching on the two sides leaves it unsolved.

The fix is a change of target, not of lemma. Land the descent in the
SQUASH — proof irrelevance closes that well-definedness for free — and
recover the datum afterwards, since the order is decidable:

```
leQUnsquash : (x y : El Q) → Prf ∥El (LeQ x y)∥ → El (LeQ x y)
```

(decide with `sgnCases`; in the refuted branch open the squash, which
is legal because ⊥ is a proposition, and re-enter the data type through
`leQOfFalse`). `ratCeil.leQBound` is proved exactly this way.

Generalisable: **a descent into a decidable data type should be stated
squashed and unsquashed at the end.**

### B-16. [ℝ] Conversion normalises under discarded projections, and a construction can stop being elaborable

The first place where a Nova development was blocked by COST rather
than by any missing argument. ℝ's product samples at a depth
proportional to a bound on the two factors, so `rMul p q` is the pair

```
(mulSeq p q , mulReg p q)
```

whose sampling index mentions `seqBound`, which unfolds through
`qNatBound` → `qFloor` → `divN` → `dmAux`'s fuel recursion, and whose
second component is a large proof term. Conversion is by
normalisation, so every type that MENTIONS `rMul p q` pays for all of
it, even when only the FIRST projection is ever used — `REq x y` reads
`seqOf x` and `seqOf y` and never touches the witness. Measured, on
the same file:

| item | types mention | time |
|---|---|---|
| `rMulWDStep` (the whole estimate) | `mulSeq` only | ~1 s |
| `rMulWDInner` | `rMul` | ~31 s |
| `rMulWDInnerCls` (one class equation more) | `rMul` | ~3.5 min |
| `rMulComm` via `rseqEq` | `rMul` | >6 min |
| the `quot-elim` descent | `rMul` | did not finish |

So `realMul` shipped WITHOUT the descent: the mathematics was complete
(`rMul`, its regularity, and `rMulWDInner` — REq-invariance in the
second argument, which is the hard estimate) and only the two-line
`quot-elim` was missing.

**RESOLVED by strict conversion.** The prediction above was that the
fix lay outside the file, in how conversion walks terms. That is what
happened, though not in either of the two forms guessed at the time:
the licensed subset does not need a projection-aware whnf step or a
cheaper ceiling, because with δ named rather than ambient, conversion
only ever walks what the site cites — and none of these sites has any
reason to cite `ratCeil.qFloor.eq`. The same file, unchanged except
for the descent being added back:

| item | before | after |
|---|---|---|
| `rMulWDInnerCls` | ~3.5 min | free |
| `rMulComm` | >6 min | free |
| `rMulWDOuter`, `realMul`, `realMulComm`, `realMulOfQ` | did not finish | free |
| whole module | 33 s (without the descent) | **2.2 s** (with it) |

The descent needed no new mathematics and no proof-term edits — the
block was transcribed from `realAdd`'s and closed by following the
elaborator's `hint:` lines, four rounds, plus one argument-order slip
of my own (`plusComm b a`, not `plusComm a b`).

The general lesson generalises past this file: **a cost wall under an
automatic conversion is not evidence that the construction is too big.**
It can be evidence that the engine is walking terms nobody asked it to
walk. Before restructuring mathematics to fit a performance budget,
find out WHICH unfolds are being paid for.

One item still had to be reshaped rather than licensed, and it is the
same lesson as the two below: `rMulComm`'s pointwise step costs 8.5 s
written inline even under the strict engine, because the `cong` motive
puts both ceilings in the conversion. Routed through `mulSeqCommAt` —
abstract in both sequences and both depths, with the depth equality an
argument — it is free, and the call site cites exactly three unfolds.

Two smaller lessons that DID work, and are worth keeping:

* **Parameterise the factor, not just the index.** `qMulInvIdx` states
  its factor as `S c`; using it forces conversion of
  `qOfNat (S (mulPred p q))` to `qOfNat (seqBound p + seqBound q)` at
  every occurrence, and the item stops finishing. `qMulInvIdxC` takes
  the factor as a natural plus the equation `C ≡ S c`, the equation is
  proved once by `⋆` where every symbol is a variable, and the same
  item takes 6 s. This is D-3 (keep it abstract) applied for SPEED.
* **Bisect with a declared stub.** A `def` with no definiens registers
  as a lemma, so replacing one argument by a stub isolates which
  argument is expensive without proving anything. That is how the
  table above was measured.
* **`using` clauses are a profiler.** Post-strict-engine, truncating
  the file and timing, then adding or REMOVING one license, says
  exactly what a conversion is costing. That is how `rMulComm` was
  found to be 8.5 s of the module's 10.4 s.

### B-17. [ℝ] Licenses are not monotone: adding a hinted `.eq` can UNDO a proof

Building ℝ's ring laws under the strict engine, the single most
expensive mistake was assuming that citing more is never worse. It is
often worse, and the failure is silent — the item stops closing and the
report blames the chain step, not the license.

`twoKTwo` is a five-step chain whose links are `qAddComm`,
`qMulSucNat` and a `cong`. Following the elaborator's `closes by
citing` hints added `nat.+.eq`, `ratNat.qOfNat.eq` and
`rationalQ.qMul.eq`; with those in place **every one of the five steps
failed**, each reported as a bare conversion obligation `LHS ≐ RHS`
with no mention of the link. Deleting all three closed the item
instantly. The cause is the poison rule: those `.eq`s unfold the goal
into elim-vocabulary while the store lemmas are held in
SigVar-vocabulary, so nothing matches any more.

Two practical consequences:

* **A license-adding loop must be able to REVERT.** Add one license,
  re-run, and keep it only if the obligation count strictly drops.
  Adding everything a hint names and moving on produced items with
  fifteen licenses that did not close; the same items close with one.
  The hint lists what a route COULD use, not what this proof needs.
  Measured on realRing.nova after the fact: a pass that removes each
  license and keeps the removal whenever the file still elaborates
  took **48** of them out, leaving the module accepted and no slower.
  Nearly half the citations the eager loop added were doing nothing.
* **When a chain step reports `LHS ≐ RHS` and the link's statement is
  literally `LHS ≡ RHS`, suspect the `using` clause, not the link.**
  That signature — the obligation being exactly the lemma you supplied
  — means the link was not applied, and the usual reason is that the
  goal has been unfolded out from under it.

### B-18. [ℝ] Abbreviations cost licenses, so the shallow spelling wins

`dbl K` is `S (K + K)`, and seeing through it requires citing
`ratHalf.dbl.eq`. But that same citation unfolds `dbl` everywhere in
the goal, which is enough to stop `qMulSucNat` from matching one step
later (B-17). Writing `S (K + K)` in the statement instead needs no
license at all, and the deep index `mulIdx (S (K + K)) l` is the same
term the abbreviation would have produced.

Related, and worth knowing before writing any ℕ arithmetic: **`+`
recurses on its SECOND argument.** So `c + S Z` reduces to `S c` on the
nose while `S Z + c` does not, and `n + Z ≐ n` is definitional while
`Z + n ≡ n` is a lemma (`zeroPlusId`). Choosing the reducing order
turned `qOfNatSuc` from an open obligation into `⋆`.

### B-19. [ℝ] `a ≡ b ∈ T → U` parses as an equation AT a function type

Cost an hour, and the error never mentions the arrow. Writing a
hypothesis that is an equation,

```
def f : (p : El RSeq) (q : El RSeq) →
  class p ≡ class q ∈ El Real → Prf (REq p q) ≔ …
```

the `∈` swallows everything to its right: the ascription becomes
`El Real → Prf (REq p q)`, so the definition's type is a single
equation at a FUNCTION type and takes no third argument. What the
elaborator then reports is whatever the body's first term hits —
here `class p` checked against a Π, i.e.

  `class checked against a non-quotient type`

with no hint that a parenthesis is missing. Adding `real.Real.unfold`,
`real.REq.unfold` and every other plausible license changes nothing,
because nothing is wrong with the quotient.

**Parenthesise every equation used as a hypothesis**:
`(class p ≡ class q ∈ El Real) → Prf (REq p q)`. The same trap in
return position is already known (SKILL: "equality-typed motives and
λ-bodies need parentheses"); this is the argument-position form, and
it is worse because the reported error names a term the author did not
write down.

### B-20. [ℝ] A dependent motive over a witness type is a rewrite the kernel will not replay

Bracketing ℝ's positivity, the natural descent is a quot-elim on x
with motive `z. El (PosR z) → El Real`. It elaborates, and then the
well-definedness obligation is

  `El (PosPayload (class p)) ≐ El (PosPayload (class p'))`

— a TYPE equation, provable only by rewriting `class p` to `class p'`
underneath `prfC (LeR … (class p))`, which is a quotient inside a
quotient. Every attempt reports `replay failed: kernel: bad path` or
`bad or type-undetermined path` (B-1 again, at the level of types).

The fix is to stop transporting the witness: put the REPRESENTATIVE
inside the payload,

```
PosPayload x ≔ ((p : RSeq) ⨯ (k : ℕ) ⨯ prfC (…) ⨯ Id Real (class p) x)
```

so the descent is ONE brElim and there is no dependent motive at all.
The payload's `Id Real (class p) x` component is what ties it to x,
and it costs nothing at use sites because it is what the caller
already has.

Two things fall out of this that are worth having anyway:

* **ℝ's quotient is effective**, and cheaply: `reqOfClassEq` transports
  `reqRefl p` along the class equation through a motive built by
  quot-elim into Ω, well-defined by `reqTrans`/`reqSym`. Any quotient
  by an equivalence relation admits the same three-line argument.
* Constancy for the bracket then reads exactly as the two theorems one
  wants: representative-invariance (`rSqrtWDK`) composed with
  modulus-invariance (`rSqrtConstK`).

## C. Discharge-engine ergonomics

### C-1. Oriented rewriting means library lemmas need flipped copies

Rewriting is left-to-right and size-decreasing, so any library lemma
stated in the size-*increasing* direction never fires. `nat.nova`
states distributivity and successor-multiplication that way, so the
development had to carry:

```
distribBack   : n * m + n * k ≡ n * (m + k)
distribBackR  : m * n + k * n ≡ (m + k) * n
sucMultBack   : m + n * m ≡ S n * m
```

Each is provable by `⋆` (the original fires via whole-equation match on
the flipped goal) — pure boilerplate.

**Suggested fix:** ship both orientations in `nat.nova`, or let the
engine try a candidate in either direction when the L→R instance is
size-increasing.

### C-2. Permutative facts never rewrite — every rearrangement is manual

Commutativity and associativity fire only by whole-equation match, so
any regrouping of a product or sum must be spelled out as a chain of
`cong`/`trans`. The ℚ development accumulated roughly fifteen lemmas
whose only content is a permutation:

`swap4`, `swap4b`, `plusSwapRight`, `mulComm2`, `sum4Distrib`,
`sum4DistribR`, `collectL`, `mulSwapHead`, `mulSwapInner`,
`mulSwapOuter`, `mulHoist`, `mulShiftL`, `assocRep`, `magAssoc`, …

Distributivity of ℚ would have needed a **seven-factor** permutation
head-on; it was only tractable after noticing that both components of
the right-hand side are the left-hand side's scaled by `d₁`, which
reduces it to the three-factor `mulShiftL`.

**Suggested fix (highest leverage after A-4):** AC-normalisation for
operators declared commutative/associative. This would delete most of
the above and shorten several proofs by an order of magnitude.

### C-3. The store is positional

A lemma helps only items *below* it. Moving `intAddZeroL` above the
scaling lemmas changed a failure into a success. Fine as a rule, but it
means the fix for an obligation is sometimes "reorder the file", which
is not discoverable from the error.

### C-4. Obligations print normalised, so lemmas must be stated normalised

Documented in the skill, still a cost: the reported goal is δ-expanded
and normalised, so `a₂ * b₂` appears as
`ℕ-elim Z (n ih. (ℕ-elim (a .π₂) (m rec. (S rec)) ih)) (b .π₂)`, and one
must reconstruct the intended statement before writing the lemma.

---

### C-5. [ℝ] Pay the Archimedean argument once, in a criterion

The shape that made ℝ's ring laws tractable, and the one to reach for
whenever a law compares two quotient representatives sampled at
different depths.

Every ring law on Bishop reals has the same difficulty: the two sides
sample at depths computed from their own factors, so the honest
pointwise estimate carries a constant built from those factors' bounds
— `(A + B) + (A + C)` for distributivity, `A·B + C·(A + B)` for
associativity — and REq demands the constant 2. Removing the slack
needs the Archimedean principle, and doing that inside each law means
writing the same three-leg chain-through-a-deep-index every time.

Instead, state the criterion once:

```
reqOfClose : (u v : El RSeq) (K : ℕ) →
  ((n : ℕ) → El (Bnd (qMul (qOfNat K) (rBound n n))
                     (qAdd (seqOf u n) (qNeg (seqOf v n))))) →
  Prf (REq u v)
```

"within K·rBound n n at every index, for ANY constant K" — and each
law becomes a pointwise estimate with no limit argument at all.

What makes it cheap is that the slack closes EXACTLY rather than by an
inequality. Chaining through a deep index N gives
`rBound n n + (2K + 2)/(N + 1)`, and at `N = mulIdx (S (K+K)) l` the
factor `S (S (K+K))` is 2K + 2, so `qMulInvIdx` turns that second
summand into `1/(l + 1)` on the nose. No comparison between fractions
is needed anywhere in the criterion, which matters because general
monotonicity of `n ↦ 1/(n+1)` is NOT in the corpus and is awkward to
prove — while the exact-factor identity was already there.

The same trick covers the deepenings the laws actually use: every
index that occurs is `mulIdx c ·` or `dbl ·`, and both have exact
factor identities (`qMulInvIdx`, `qInvHalf`), so `1/(φ m + 1) ≤
1/(m + 1)` follows from "multiplying a nonnegative by S c ≥ 1 only
grows it" rather than from any inequality between denominators.

## D. What the workarounds look like (worked examples)

### D-1. Getting a disequality out of a quotient

Wanted: `¬ (intOne ≡ intZero ∈ El Int)`. Blocked at the time by
A-3 + A-4: the natural `quot-elim` into `Ω` owed a propext instance.
(Both are since resolved — the disequality itself is now immediate from
effectivity. The construction below is kept because what it produces is
a canonical form as DATA, which effectivity does not give.)

The route that works: extract the canonical representative as a **pair
of nats** rather than deciding inside `Ω`.

```
def intCanon : El Int → ℕ ⨯ ℕ ≔
  λz. quot-elim (w. ℕ ⨯ ℕ) (p. normPair (p .π₁) (p .π₂)) z
```

Its well-definedness is `normPair a b ≡ normPair c d` whenever
`a + d ≡ b + c` — a **ℕ-level** equation, provable by induction, with
no propext anywhere. Comparing canonical pairs componentwise with
`EqN` then gives a relation that genuinely reduces to ⊤/⊥, hence a real
disequality.

Generalisable lesson: when an `Ω`-valued quotient eliminator is
blocked, look for a **`𝕌`-valued canonical form** whose well-definedness
is an ordinary equation.

### D-2. Avoiding an eight-way sign case split

`nzMul`'s magnitude law (associativity of stored magnitudes) is a
seven-monomial permutation:

```
(mk+m+k)·l + (mk+m+k) + l ≡ m·(kl+k+l) + m + (kl+k+l)
```

Proving it directly is grim. Going through **successors** makes it five
steps: `S` of each side is a product of `S m`, `S k`, `S l` by
`sucMulSuc`, `multAssoc` equates those, and `S` is injective
(`predEq`). The eight sign cases then all reuse the one magnitude law.

### D-3. Keep representatives abstract; instantiate by application

The single most reliable technique found. Whenever a statement would
mention a big non-inferable term (a `quot-elim` spine, a δ-expanded
definition), state the lemma over a **variable** and instantiate it in
one application:

```
def intNZViewAt : (z : El Int) (p : ℕ ⨯ ℕ) (hz : Prf (class p ≡ z ∈ El Int)) … 
def intNZView   : … ≔ λz. λhnz. intNZViewAt z (intCanon z) (intCanonClass z) …
```

Inside the abstract lemma every conversion is between small
variable-headed terms, so both the engine and the kernel cope; at the
call site the elaborator only substitutes. Taking the representative
as a *pair* rather than as two projections matters for the same
reason — `class (p .π₁ , p .π₂)` with `p` a variable is fine, the same
spelling with `p ≔ intCanon z` is not (B-6).

This one rewrite turned three stuck obligations into `Accepted.`

### D-4. Replace a squashed existential with a data-valued view

`Prf ∥(e : El NZ) ⨯ Prf (nzToInt e ≡ z)∥` says an integer is the image
of some non-zero one; `((e : El NZ) ⨯ Prf (nzToInt e ≡ z)) ⊎ Prf (z ≡ 0)`
*decides* it and hands back the witness as data. The second is
definable for the same reason the first is — the case analysis runs on
`intCanon z`, an ordinary **function** `El Int → ℕ ⨯ ℕ` — so no extra
well-definedness obligation appears, and nothing is erased.

That one change is what turns "an inverse exists" into "here is the
inverse": with the view in hand, `invRep` can branch on the numerator's
sign, and `qInv : El Q → El Q` becomes a real function.

Whenever a squashed existential is about to be introduced, check
whether the witness can be *computed* instead: a `⊎` of `Σ`s costs the
same proof effort and yields an algorithm.

### D-5. Making a quotient descent cheap

For `qAdd`, the *outer* well-definedness obligation was discharged for
free by `ratAddComm`: commuting turns it into the inner case with the
arguments swapped. Worth remembering whenever an operation is
commutative — it halves the descent work.

### D-6. [ℝ] Squash the witness; land the use in a DECIDABLE type

The Archimedean property of ℚ — every positive `u` dominates some
`1/(k+1)` — is a function producing an index, so the obvious statement
is a Σ. It cannot be one: the index depends on the *representative*
(½ and 2/4 name 2 and 4), and `quot-elim` into a Σ-code owes a
well-definedness proof that is false. The statement must be

```
qArch : (u : El Q) → (sgnQ u ≡ sPos ∈ El Sign) → Prf ∥El (ArchWit u)∥
```

which, by A-5/F-2, can then only be eliminated into a `Prf`. That looks
fatal for the intended use — deriving an ORDER fact `LeQ a b`, which is
data (a `⊎` of `Id`s).

It is not, and the escape is reusable. The order is **decidable**
(`sgnCases`), so the use runs as: decide; in the good branch return the
verdict; in the bad branch derive `Prf ⊥` (there the squash may be
eliminated, since ⊥ is a proposition) and then re-enter the data type
through the equation it is built from —

```
leQOfFalse : (x y : El Q) → Prf ⊥ → El (LeQ x y) ≔
  λx. λy. λf. inj₁ (eqToId Sign (sgnQ (qAdd y (qNeg x))) sZero
                     (absurdP (sgnQ (qAdd y (qNeg x)) ≡ sZero ∈ El Sign) f))
```

`absurdP` gives the *equation* the constructor wants, and `inj₁` gives
the datum. So F-2's "a `Prf ⊥` can never produce data" is true only for
an arbitrary type: for a type whose constructors are indexed by
equations — which every order/sign verdict in this corpus is — ⊥ does
reach it.

Rule of thumb: a squashed existential is harmless whenever the theorem
it proves is decidable. Decide first, squash-eliminate only inside the
refuted branch.

### D-7. [ℝ] Two-sided bounds instead of an absolute value

`|u| ≤ b` has no good definition here: `qAbs` would need a sign case
split, and every triangle inequality would then be a four-way case
analysis. Defining instead

```
Bnd : El Q → El Q → 𝕌 ≔ λb. λu. (LeQ (qNeg b) u ⨯ LeQ u b)
```

makes the triangle inequality a *pair of independent monotonicity
steps* (`bndAdd`) with no case analysis at all, and the two halves
never interact. Regularity and closeness in `real.nova` were already
written in exactly this shape by hand; naming it turned four-line
in-line pairs into `bndAdd`/`bndVia`/`bndWeaken` applications and made
the addition and transitivity proofs readable.

Generalisable: in a linearly ordered setting with no decidable
absolute value, prefer the *conjunction of two inequalities* as the
primitive. It is definitionally the same thing and proof-theoretically
much cheaper.

### D-8. [ℝ] Define the relation one level UP, not on representatives

The textbook definition of `<` on the reals is about representatives:
*some* index n at which y_n beats x_n by more than the modulus. Stating
it that way means owing a proof that it survives the quotient relation,
and for `<` that proof is genuinely hard — it needs a quantitative
"pick a deeper index" argument of its own.

Stating it one level up instead —

```
LtR u v  ≜  ∥(k : ℕ) ⨯ Prf (LeR (realAdd u (realOfQ (qInvNat k))) v)∥
```

— makes invariance FREE: every constituent (`LeR`, `realAdd`,
`realOfQ`) already lives on ℝ, so there is nothing to descend. The
whole of `realLt.nova` is then ~180 lines with no representative in
sight, and the only place the Archimedean property is spent is the
single lemma relating it back to `<` on ℚ.

The same reading explains why `realAbs.nova` is short and `realOrder.nova`
is not: `|·|` is 1-Lipschitz, so it commutes with the quotient
structure on the nose, while `≤` does not and had to be repaired by
`leQOfArch`. **Before descending an operation to a quotient, check
whether it can be assembled from operations that have already
descended.**

### D-9. [ℝ] What a quotient blocks, and what it does not

Two facts about ℝ needed care about *where* the quotient sits, and the
distinction is worth stating once.

**Completeness needs representatives.** "Every regular sequence of
reals converges" cannot be stated for an arbitrary `X : ℕ → El Real`:
building the limit needs a rational approximation of each `X n`, i.e. a
choice of representative for each n, i.e. countable choice, and the
quotient has no section. `realComplete.nova` therefore states it for a
sequence given WITH representatives (`ℕ → El RSeq`) — which is the
constructive content anyway, and is what any caller who built the
sequence actually has.

**Multiplication does NOT need a canonical form.** The PR draft claimed
it needed lowest terms for ℚ, hence gcd. That was wrong. What the
product needs is a natural bounding each factor, computed from a
rational by a function the quotient respects — and the CEILING is such
a function, needing only Euclidean division (natDiv.nova), not gcd.
`ratCeil.qNatBound` is that function and `realBound.seqBound` is the
resulting bound on a regular sequence.

The moral: before declaring a quotient blocks a construction, ask
which invariant is actually required. "A canonical representative" is
usually much more than the construction needs.

---

## E. Elaborator ergonomics

### E-1. `_` is solved from the ARGUMENTS, never from the goal

An index written `_` is filled only when some *later argument's* type
pins it. The expected type of the whole application never contributes:

```
def idLemma : (a : ℕ) → a ≡ a ∈ ℕ ≔ λa. ⋆
def probeId : (x : ℕ) → x ≡ x ∈ ℕ ≔ λx. idLemma _    -- ? : ℕ, unsolved
```

The goal `x ≡ x ∈ ℕ` determines `a ≔ x` first-order — no El-decoding, no
defined function in the way — and the hole still survives to the report.

**Mechanism.** `convTy` (Elaboration.idr) runs `attemptT` first and
reaches the solver only when the attempt FAILED:

```
r <- attemptT ctx site tyA tyB
case r of
  Right cert => pure (Just cert)        -- holes never touched
  Left site1 => do solved <- patternSolveT ...
```

For an equation-typed conclusion the attempt succeeds **vacuously**:
code-prop-eq equates any two true propositions, and `Prf (_h ≡ _h ∈ ℕ)`
and `Prf (x ≡ x ∈ ℕ)` are both reflexivity instances, hence both true,
hence equal codes. The conversion is discharged without ever looking at
`_h`.

`sym _ _ _ h` works for the complementary reason: there the holes meet
`h`'s type while still *un*related (`_a ≡ _b` is not evidently true), so
`attemptT` fails, `patternSolveT` runs, and Miller inversion fills them.

So the rule is exact: **an index of an equation-typed lemma is
recoverable iff some proof argument mentions it.** Which is also why
`intMulCong2 _ _ _ _ ⋆ h` leaves the reflexive side unsolved — `⋆`
mentions nothing.

**Two candidate fixes**, in increasing order of ambition:

1. When solvable holes are in play, run the solving pass BEFORE
   `attemptT` (or again after a vacuous success). Cheap, and fixes every
   case where a side IS a hole.
2. Extend the solver to congruent decomposition on the UNNORMALIZED
   spine, so `intMul _a _b ≟ intMul z x` solves componentwise. This is
   what the remaining residue needs: after β the two sides are stuck
   `quot-elim`/`ℕ-elim` spines with no rigid head left to match, so
   nothing fires. Solving is only a guess that the following `attemptT`
   verifies, so decomposition costs nothing in soundness.

**Measured** by blanking every index position in the ℚ development and
keeping what still elaborates (see the `blank.py` sweep in the session
notes): most go. The residue is exactly the arguments of the arithmetic
lemmas — `assocRep`, `distribBack`, `multAssoc`, `intMulComm`, … — whose
indices appear in the conclusion only under `+`, `*` or `intMul`. Fix 2
is what would collect those.

### E-1½. Holes are the most expensive surface feature to elaborate

Follow-up to E-1, on the COST axis (measured; full anatomy in
PerfNotes "The cost of a hole"): the heaviest proof item of the corpus
spends ~98% of its 458ms on its ~16 blanked indices — the identical
combinator spine with indices spelled runs in 10ms. The blanking sweep
made the heavy files ~2–3× slower to elaborate overall.

Cause, briefly: each hole pays a full doomed discharge attempt before
the solver runs (E-1's ordering), each solved hole's in-place Σ flip
wipes the normal-form caches, an unsolved hole starves the free
conversion tiers, and late solves re-elaborate the whole item.

**Suggested fix:** E-1's candidate fix 1 (solve before the attempt when
a side is an unsolved-hole spine) now pays twice — completeness AND
the attempt tax; plus dependency-scoped cache eviction on flips.
Until then: on hot items, spell the indices — `_` is cheap to write
and expensive to elaborate.

### E-1¾. [ℝ] `transport` at a `Prf`-valued family fails as a λ error

`transport`'s family is `El A → 𝕌`; for a family landing in `Ω` the
combinator is `transportP`. Reaching for the wrong one —

```
transport Real (λw. LeR (realOfQ p) w) …          -- LeR : … → Ω
```

— is diagnosed as

```
λ checked against a non-Π type (ascribe the term: `(t : T)`)
```

which points at the λ rather than at the family's sort. Same class of
mis-pointing as F-1 was.

### E-2. Proof terms are enormous because every hop repeats its endpoints

A five-step calculation becomes a thirty-line nested `trans`, each
level restating two large terms that the reader (and the elaborator)
could infer. `crossAssocNum`, `assocRep`, `distribNum` are each ~30
lines expressing about five real steps.

**Suggested fix:** a calc-style chain form, e.g.

```
chain x ≡⟨ lemma1 ⟩ y ≡⟨ lemma2 ⟩ z
```

`let` (which is judgementally transparent — see `letExpr.nova`) helps
name subterms but does not remove the repetition in `trans`.

---

## F. Syntax

### F-1. λ bodies do not extend past `⨯` — RESOLVED

```
cong ℕ (λu. ℕ ⨯ ℕ) …
```

parses as `(λu. ℕ) ⨯ ℕ`, and the resulting error is
`λ checked against a non-Π type (ascribe the term: (t : T))`, which
points nowhere near the cause. `(λu. (ℕ ⨯ ℕ))` is fine. The known
pitfall about parenthesising equality-typed λ bodies applies to
Σ-codes too.

**Suggested fix:** either let λ bodies extend maximally, or mention the
enclosing operator in the error.

**Resolution:** λ and let-in bodies now extend maximally — over
operators, the code formers, ≡-elements, calc chains, and pairs. The
one price is the Agda/Haskell convention that came with it: a λ that
is a NON-FINAL pair component must be parenthesised (`(λx. e) , f`),
and the corpus's structure-instance tuples were migrated accordingly.

*Checked and NOT a problem:* multi-binder Π sugar inside an eliminator
motive (`(k. (m : ℕ) (n : ℕ) → …)`) parses and elaborates fine.

### F-2. `Prf ⊥` is not `𝟘`

`⊥ ≜ ∥𝟘∥`, so `𝟘-elim` cannot consume a `Prf ⊥` directly — the
diagnostic is `Prf (prop.⊥) ≐ 𝟘 type`. The idiom is
`squash-elim h (t. 𝟘-elim t)`, and it is needed at every refutation.
**Resolved:** `prop.nova` now has `absurdP : (p : Ω) → Prf ⊥ → Prf p`.

There is no `El A`-valued counterpart *of that shape*: `el-squash-e-prf`
reaches only further *propositions*, so no elimination of the proof
produces data. ⊥ itself is not data-inert, though — `prop.absurd :
Prf ⊥ → 𝟘` goes around the eliminator (⊥ proves the false equation
`Z ≡ S Z ∈ ℕ`, `el-reflect` makes it judgemental, `isZeroCode`
transports `()` from `𝟙` into `𝟘`), and `prop.absurdD : (A : 𝕌) →
Prf ⊥ → El A` follows by `𝟘-elim`. So a refutation that must yield an
element can either keep the raw `𝟘` around, as `nzOfPairD` does with
`zNotS`, or call `absurdD`.

### F-3. `⋆` does not prove Σ-shaped squashes

`Prf (p ∧ q)` needs `andIntro _ _ ⋆ ⋆`. The error message says exactly
this and is one of the better diagnostics in the system.

### F-4. [ℝ] A Σ-CODE binds over a code; a Σ-TYPE binds over `El` — and
mixing them reports `unknown name`

Both spellings occur throughout the corpus and they are not
interchangeable:

```
def T : 𝕌 ≔ ((m : Int) ⨯ Id Int m m)                 -- code:  domain is a CODE
def V : (z : El Int) → ((e : El NZ) ⨯ Prf (…)) ⊎ …   -- type:  domain is El CODE
```

Writing the second form where a code is expected —
`def T : 𝕌 ≔ ((m : El Int) ⨯ Id Int m m)` — fails with

```
Error: def T: unknown name 'm'
```

i.e. the binder is silently not a binder, and the error points at the
*use* of `m`, several lines away, with no mention of `⨯` or of codes.
This cost the most wall-clock of anything in the ℝ development per
character typed, because the message sends you looking for a missing
import.

**Suggested fix:** when a `⨯`/`→` domain in code position is an `El`
application, say "a Σ-code binds over a code; drop the `El`" rather
than failing on the body.

---

## G. Diagnostics

### G-1. Kernel rejections dump raw core terms

A single rejection printed several hundred characters of
`Prf (EqTy (SigmaIntro (QuotElim (Class (SigmaIntro (NatElim …`. The
information needed — *which* step, at which source position, and the
two sides in surface syntax — is absent.

### G-2. An unsolved metavariable surfaces as an internal crash

`impApply _ _ hnz ⋆` left a metavariable unsolved and the run died with

```
ERROR: betaElem: signature identifier '_r61c47' not found
```

— a hole name leaking into evaluation. The name does encode a source
position, which is how it was tracked down, but this should be an
"unsolved metavariable at …, expected type …" diagnostic, not a crash.

### G-3. Failed class-equality goals decompose into alarming nonsense

When a `class a ≐ class b` goal fails, the report lists sub-goals like
`p .π₁ ≐ p .π₂` and `c₂ ≐ c₁`, which are not what one is trying to
prove and look like a soundness problem at first glance. The useful
line is the `from composite:` one.

**Suggested fix:** report the composite goal first (or only), and mark
the decomposed residue as such.

---

## H. Library gaps encountered

Things that had to be built before the actual development could start:

* `integer.nova` had no `intZero`, `intOne`, `intNeg` — added.
* **No integer multiplication at all.** `integerMul.nova` was written
  from scratch: two well-definedness proofs (both needing distributive
  regrouping, unlike addition's) plus the ring laws.
* `nat.nova` lacks right distributivity, `S Z * m ≡ m`, and any
  cancellation lemma; `S`-injectivity lives in `eqNat.nova`, not `nat`.
* No generic congruence combinators — `mulCongL/R`, `plusCongL/R`,
  `intAddCong2`, `intMulCong2`, `classCong2`, `pairEq2` are all
  one-line `⋆`s that every development will re-invent. These belong in
  `equality.nova`, generically.
* No generic Σ-η (`pairEta`) — see B-3 for why the specific version is
  actively dangerous.
* **[ℝ]** `rationalOrder.nova` had `LeQ` with reflexivity, totality,
  transitivity, antisymmetry and monotonicity, but none of: negation
  reversal (`leQNegFlip`), two-argument addition (`leQAdd`),
  `0 ≤ b → a ≤ a + b` (`leQSelfAdd`), or nonnegativity from a positive
  sign (`leQZeroOfPos`). All four are three-line transports and all
  four are needed before any bound algebra can start; they now live in
  `ratBound.nova`.
* **[ℝ]** No Archimedean property for ℚ, and nothing that computes a
  unit fraction below a given positive rational. `ratArch.nova` builds
  it from `intNonZero`'s decision plus a denominator-sign
  normalisation (`qNegDen`); ~200 lines, and it is the prerequisite for
  every fact about ℝ that is not an index shift.

---

## I. What works well (for balance)

* **Extensional reflection earns its keep.** `sym`, `trans`, `cong`,
  `transport`, and every congruence combinator is a single `⋆`. Chains
  are verbose but each link is free.
* **`⋆` closes a lot at the representative level.** Quotient
  well-definedness goals that look frightening (`intMulDistribL`'s
  eight-term identity) often go through untouched.
* **Quotient descent is mechanical** once the relation-level lemma is
  in hand: `clsEqOfRel` + `quot-elim` at an `≡`-motive, every time.
* **Structural encodings are cheap.** `NZ ≔ ℕ ⊎ ℕ` made closure under
  multiplication *definitional* — no side conditions to discharge
  anywhere in the ℚ development.
* **Error text for surface-level mistakes** (holes, unknown names,
  `⋆`-misuse) is precise and actionable. It is only the
  engine/kernel-boundary failures (B) that are opaque.
* **[ℝ] The calc chain carries most of a real development.** Nearly
  every lemma in `ratBound`/`ratArch`/`realAdd` is a `≡⟨ ⟩` chain, and
  they read as the mathematics does. E-2's complaint is answered.
* **[ℝ] Quotient descent scales.** ℝ is a quotient of a Σ over a
  function space into a quotient of a Σ over a quotient of ℕ ⨯ ℕ, four
  levels deep, and the descent recipe (`clsEqOfRel`-analogue +
  `quot-elim` at an ≡- or Ω-motive + an inner/outer well-definedness
  pair) worked unchanged at every level. Ten operations descended
  without a single new idea.
* **[ℝ] Ω-valued relations descend by `propExt` with no friction.**
  `LeR` is a `quot-elim` into `Ω` in both arguments; the two
  well-definedness goals are `propExt` applied to the two transfer
  lemmas, and that is the entire descent. A 𝕌-valued order could not
  have descended at all — there is no univalence — so the Ω/𝕌
  distinction, which reads as a restriction elsewhere, is what makes
  the order on ℝ definable.
