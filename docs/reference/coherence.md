# Types without coherence

In an intensional theory, dependent types make you write proofs *inside
types*. An index does not line up, so you insert a `subst` into the
statement to repair it — and because that `subst` is stuck on a proof
that is not `refl`, it survives into every downstream term, where it
has to be reasoned about with further lemmas about `subst` itself.
That is the coherence tax, and it is the reason "just index your
vectors by their length" is easy advice and hard practice.

Nova does not charge it. Reflection makes the repairing equation
judgemental, `transport` is the identity function, and the coherence
proofs that would have lived in your types simply have nowhere to sit.

This chapter is a tour of where that shows up.

## The problem, stated intensionally

Take vector append. Its type mentions an addition:

```text
_++_ : Vec A n → Vec A m → Vec A (n + m)
```

and now try to state that it is associative. The left side has length
`(n + m) + k`, the right side `n + (m + k)`. Those are propositionally
equal and *not* judgementally equal, so the two sides do not even
inhabit the same type — the statement does not typecheck. The standard
repairs are to cast in the statement:

```text
++-assoc : (xs : Vec A n) (ys : Vec A m) (zs : Vec A k)
         → cast (+-assoc n m k) ((xs ++ ys) ++ zs) ≡ xs ++ (ys ++ zs)
```

or to switch to heterogeneous equality, which defers the same problem
to wherever you need a homogeneous equation again.

Either way the damage is done. `cast` is stuck unless its proof
reduces to `refl`, so it does not compute away; it shows up in the
induction step, where you now need lemmas relating `cast` to
consing, to composition, to itself. Each new statement about `++` owes
its own coherences, and they multiply with the number of indices.

## Why it disappears

Two facts from [Equality](#equality), applied together.

First, a proved equation is a judgemental one. If `plusAssoc` is in
scope, then `(n + m) + k` and `n + (m + k)` **are** the same natural
number as far as the checker is concerned, so `vect ((n + m) + k) A`
and `vect (n + (m + k)) A` are the same type — by congruence, no
coercion involved.

Second, the repair, if you ever write it, is the identity:

```nova
def transport : {A : 𝕌} (P : A → 𝕌) {a b : A} → (a ≡ b) → P a → P b ≔ λA. λP. λa. λb. λh. λp. p
```

There is no stuck term to get in the way, because there is no term. A
statement that would have needed a cast can be written without one, and
the proof of it is a proof about vectors rather than a proof about
casts.

## Example: defining append

`vectByInd.nova` builds vectors by recursion rather than as a
constructor family, which sharpens the point — nothing here is
definitional by pattern matching:

```nova
def vect : ℕ → 𝕌 → 𝕌 ≔ λx. λy. ℕ-elim 𝟙 (n ih. y ⨯ ih) x
```

Append is an induction on the first length:

```nova
def vappend : (n : ℕ) {A : 𝕌} (m : ℕ) → vect n A → vect m A → vect (n + m) A
  using (nat.+.unfold, sucPlus.rw, vect.eq, vectByInd.vect.unfold, zeroPlusId.rw) ≔
  λn. λA. λm. ℕ-elim (λv. λw. w) (k ih. λv. λw. v .π₁, ih (v .π₂) w) n
```

Look at the two cases against the types they are checked at.

- **Base.** The body is `λv. λw. w`, so `w : vect m A` is checked
  against `vect (Z + m) A`. Those are not definitionally equal: `+`
  recurses on its **second** argument, so `Z + m` is stuck. In an
  intensional setting you would write
  `subst (Vec A) (sym (+-identityˡ m)) w`. Here you write `w`.
- **Step.** The body is a pair, of type `A ⨯ vect (k + m) A`, checked
  against `vect (S k + m) A`. Again not definitional: it needs
  `S k + m ≡ S (k + m)`. In an intensional setting, another `subst`.
  Here, a pair.

Now read the `using` clause again. `zeroPlusId.rw` and `sucPlus.rw` are
*exactly* the two equations the intensional definition would have had
to insert as coercions, and `vect.eq` / `vect.unfold` are the
unfoldings that pattern matching would have given for free.

> The cost has not vanished into thin air — it has moved out of the
> **term** and into the **licence list**. That is the trade: the
> equations are still yours to prove and to name, but they stay at the
> edge of the definition instead of being woven into it.

The β-lemmas are stated the same way, with no cast in sight:

```nova
def vappendZ : (A : 𝕌) (n : ℕ) (v : vect Z A) (w : vect n A) → vappend _ _ v w ≡ w ∈ vect n A
```

The left side of that equation has type `vect (Z + n) A` and the right
`vect n A`. The `∈ vect n A` annotation picks one, and the statement is
well-formed because the two are the same type once `zeroPlusId` is in
scope.

## Example: associativity, stated without a cast

Here is the lemma that motivated the chapter, verbatim from
`vectByIndAppend.nova`:

```nova
def vappendAssoc : (n : ℕ)
  (A : 𝕌)
  (m k : ℕ)
  (v : vect m A)
  (w : vect k A)
  (u : vect n A)
  → vappend _ _ (vappend _ _ u v) w ≡ vappend n (m + k) u (vappend _ _ v w)
  using (hyp.rw,
    nat.+.unfold,
    plusAssoc,
    plusAssoc.rw,
    sucPlus,
    sucPlus.rw,
    vappendS.rw,
    vappendZ.rw,
    vect.eq,
    vectByInd.vect.unfold,
    zeroPlusId,
    zeroPlusId.rw) ≔
  λn. λA. λm. λk. λv. λw. λu. (ℕ-elim (p. (q : vect p A)
    → vappend
      (p + m)
      k
      (vappend _ _ q v)
      w ≡ vappend _ _ q (vappend _ _ v w) ∈ vect (p + (m + k)) A)
    (λq. ⋆ using (vappend.eq, vect.eq, zeroPlusId.rw, sucPlus.rw, hyp.rw))
    (p ih. λq. vappendAssocS (ih (q .π₂)))
    n)
    u
```

Points worth dwelling on:

- **The statement is the statement.** `vappend _ _ (vappend _ _ u v) w`
  and `vappend n (m + k) u (vappend _ _ v w)` sit at intensionally
  different lengths, and the type is written anyway. It is well-formed
  because `plusAssoc` is named; the source comment in the corpus puts
  it plainly — the statement "only type-checks up to
  plus-associativity", and the imported `plus` lemmas discharge the
  mismatch.
- **The motive is an ordinary equality motive.** `(p. (q : vect p A) → …)`
  quantifies over the tail vector and states the equation at
  `vect (p + (m + k)) A`. No `PathP`, no cast-over-a-path, no
  `subst`-in-the-motive.
- **The base case is `⋆`.** With the length equations licensed, both
  sides compute to the same term.
- **The step case passes the induction hypothesis as an equation.**
  `vappendAssocS` takes the tail instance of the ih and returns `⋆`:
  once the ih is in scope it is reflected, so both sides — cons cells
  whose tails the hypothesis relates — are judgementally equal.

The intensional version of this proof spends most of its length moving
casts around. This one has no cast to move.

## Example: eliminator coherences are `⋆`

The same thing happens one level up, in the methods you pass to an
eliminator. A QIIT with an equation constructor:

```nova
data [a : 𝕌] ( Bag : U
     ; nil : El Bag
     ; ins : a → El Bag → El Bag
     ; swp : (x : a) (y : a) (m : El Bag) → ins x (ins y m) ≡ ins y (ins x m) ∈ El Bag )
```

To define a function out of `Bag` you must say what it does on the
equation constructor — the coherence. In a path-based setting that
method is a dependent path over `swp`, a term you have to *build*, and
building it is where transports reappear. In Nova the coherence is an
ordinary equality-typed argument, so it is `⋆` whenever the method is
insensitive to the imposed equation:

```nova
def size : (a : 𝕌) → Bag a → ℕ using (qiitBag.Bag.unfold) ≔
  λa. λm. BagElim a (λb. ℕ) Z (λx. λr. λih. S ih) (λx. λy. λr. λih. ⋆) m
```

When the coherence is *not* free, it is still an ordinary equational
goal, discharged like any other. `qiitInt.nova` defines negation over
integers presented with `suc`/`pred` and two invertibility equations,
and each coherence is closed by the other equation:

```nova
def neg : I → I using (predsuc, qiitInt.I.unfold, qiitInt.pred.eq, qiitInt.suc.eq, sucpred) ≔
  λi. IElim (λw. I) zero (λx. λih. pred ih) (λx. λih. suc ih) (λx. λih. ⋆) (λx. λih. ⋆) i
```

And for equational goals the coherences do not merely become trivial —
they do not exist. Every sort gets a second, prop-valued eliminator
`<Sort>ElimP` whose motives land in `Ω`, and it takes **no coherence
arguments at all**, because proof irrelevance already closes them
([Quotient inductive-inductive types](#qiits)).

## Example: quotient lifts carry the respect proof, and nothing else

The generic lift out of a quotient, from `qiitQuot.nova`:

```nova
def qlift : (a : 𝕌)
  (r : a → a → Ω)
  {b : 𝕌}
  (f : a → b)
  (resp : (x y : a) → r x y → f x ≡ f y)
  → Q _ r → b
  using (qiitQuot.Q.unfold) ≔
  λa. λr. λb. λf. λresp. λq. QElim a r (λw. b) (λx. f x) (λx. λy. λh. resp x y h) q
```

The coherence argument **is** the caller's respect proof, handed
through unchanged. There is no wrapping, no transport of `resp` along
anything, and the caller's obligation is the mathematical one — `f`
respects `r` — with nothing added on top.

The primitive quotient behaves the same way: `quot-elim`'s
well-definedness premise is a conversion judgement, so if the case
function respects the relation by computation or by an accepted lemma,
elaboration is silent, and otherwise "f respects R" surfaces as an
ordinary obligation ([Quotients](#quotients)).

And when what you descend is a **proposition** rather than data, the
premise costs nothing at all: at an Ω-valued motive the two sides
inhabit a prop instance, so proof irrelevance closes the goal outright
(`el-prf-prop`). `quotGroup.nova` states the consequence plainly —
descending data costs two honest proofs, descending a proposition
costs none — and that is why the second half of that development is
free.

## When you *do* write a transport

Occasionally you want the retyping without any computation, and then
`transport` earns its keep precisely because it is the identity. From
`realSeq.nova`, reading one sequence's regularity witness at another's
type:

```nova
(regularIsProp _ (regOf x) (transport (λf. Regular f) (sym _ _ h) (regOf y)))
```

Nothing is inserted into the term — `transport` computes to its
argument — but its *signature* performs the retyping, and the
conversion it needs was discharged once, at an abstract motive. This is
the standard move when the kernel will not replay a conversion in
place: route it through a lemma application, which is unconstrained by
position.

## What is still owed

Coherence proofs are gone. Equational content is not, and it is worth
being precise about what remains:

- **The equations are still yours.** `plusAssoc`, `zeroPlusId` and
  `sucPlus` are real lemmas with real inductive proofs. Nova removes
  the obligation to *thread* them through terms, not the obligation to
  *prove* them.
- **They must be named.** The checker will not go looking for the
  equation that repairs a mismatch. What you get instead of a type
  error is an obligation whose statement is exactly the mismatch, plus
  a hint naming what would close it
  ([The discharge engine](#discharge)).
- **η laws for QIITs and coinductive types are a separate story.**
  `el-qiit-eta` and `el-nu-eta` hold judgementally in the theory but
  carry no kernel certificate, so uniqueness-shaped goals still take
  work — see [Coinductive types](#coinduction).

## Where this comes from

The mechanism is `el-reflect` plus proof irrelevance; both are in
[Equality](#equality), and the rules themselves are in the Ω block of
`docs/NovaFoundation.txt`. The worked sources for this chapter are
`src/nova/vectByInd.nova`, `src/nova/vectByIndAppend.nova`,
`src/nova/qiitBag.nova`, `src/nova/qiitInt.nova` and
`src/nova/qiitQuot.nova`.
