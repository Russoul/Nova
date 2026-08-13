# Proving in Nova — accumulated feedback

A running log of friction encountered while *using* Nova to develop
mathematics, as opposed to specifying it. Not a spec: nothing here is
normative, and several items are consequences of deliberate design
choices rather than defects. Each entry records what happened, where,
what it cost, and — where there is one — a suggested fix.

Sources so far: the ℤ → Rat → ℚ development
(`integer.nova`, `integerAdd.nova`, `integerMul.nova`, `rational.nova`,
`rationalQ.nova`, `rationalInv.nova`) and the observational
equality/disequality of ℤ (`eqInt.nova`).

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

---

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

### B-5. Context sensitivity of proofs

Following from B-3/B-4: whether a `⋆` closes depends on the full
candidate store, which depends on imports, on item order within the
file, and on whether *other* items failed. Proofs are therefore not
stable under refactoring — moving a lemma, or adding an unrelated
import, can break a proof several items later.

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

### F-1. λ bodies do not extend past `⨯`

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

*Checked and NOT a problem:* multi-binder Π sugar inside an eliminator
motive (`(k. (m : ℕ) (n : ℕ) → …)`) parses and elaborates fine.

### F-2. `Prf ⊥` is not `𝟘`

`⊥ ≜ ∥𝟘∥`, so `𝟘-elim` cannot consume a `Prf ⊥` directly — the
diagnostic is `Prf (prop.⊥) ≐ 𝟘 type`. The idiom is
`squash-elim h (t. 𝟘-elim t)`, and it is needed at every refutation.
**Resolved:** `prop.nova` now has `absurdP : (p : Ω) → Prf ⊥ → Prf p`.

Note there can be no `El A`-valued counterpart: `el-squash-e-prf`
reaches only further *propositions*, so a `Prf ⊥` can never produce
data — for that one needs a `𝟘` itself. Refutations that must yield an
element (a `⊎`-branch, say) have to keep the raw `𝟘` around, as
`nzOfPairD` does with `zNotS`.

### F-3. `⋆` does not prove Σ-shaped squashes

`Prf (p ∧ q)` needs `andIntro _ _ ⋆ ⋆`. The error message says exactly
this and is one of the better diagnostics in the system.

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
