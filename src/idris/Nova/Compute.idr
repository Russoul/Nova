module Nova.Compute

-- A standalone computation procedure for Nova (docs/NovaFoundation.txt):
-- head-normal-form evaluation (whnf) plus a normalization procedure
-- (nf) that piggybacks off it. Not wired into the elaborator or the
-- kernel (Nova.Kernel, Nova.Elaboration) — this module only reuses the
-- term representation (Nova.Kernel.Syntax) and the pure substitution
-- algorithm (Nova.Kernel.Subst), both already standalone themselves.
--
-- ===== whnf: beta reduction in the empty context =====
--
-- whnfElem/whnfTy contract ONLY a term's own head redex chain, by
-- Foundation's ≜ rules (el-pi-beta, el-sigma-beta₁/₂, el-nat-beta-z/s,
-- el-quot-beta, el-qiit-beta, el-sig-beta (type entries included), the El-decoding
-- family) — exactly Nova.Elaboration.Beta's contraction clauses, but each
-- one stops the instant its own head is exposed, instead of also
-- descending into every subterm. A term with no head redex — every
-- canonical/constructor form (𝟘-/𝟙-/ℕ-introductions, λ, pairs, universe
-- codes, class, ∥T∥, ⋆, a QIIT sort/constructor) — is therefore
-- ALREADY in head normal form: it is returned with its own components
-- entirely unexamined. "Beta reduction in the empty context": Γ never
-- enters into it (reduction is untyped rewriting on closed syntax),
-- only Σ, for x[e˲] unfolding.
--
-- ===== nf: normalization by recursing on whnf's subterms =====
--
-- nfElem/nfTy compute whnf first, then recurse nf into every immediate
-- subterm of the result — turning "the head is normal" into "the whole
-- term is normal" one layer at a time. Concretely this often takes
-- SEVERAL rounds of whnf to fully settle a term: e.g. unfolding a
-- ℕ-elim redex at S n can expose a new head shaped `S (S (ℕ-elim …))` —
-- already head-normal (the head is S, not a further ℕ-elim), so whnf
-- stops there, and it is nf's recursion into that S's argument that
-- resumes the elimination (see Nova.ComputeTest for a worked example).
--
-- ===== Never under a binder =====
--
-- nf recurses into an IMMEDIATE subterm only when that subterm lives in
-- the SAME context as its parent. Whenever a former's rule extends the
-- context for one of its components (Foundation's Γ▷A, Γ▷ℕ▷A, …), that
-- component is left EXACTLY as whnf produced it — never recursed into.
-- Concretely, comparing against each former's presupposition:
--
--   PiTy/Elem.PiTy A B   — Γ⊦A, Γ▷A⊦B — BOTH sides left alone: Π is
--                             co-data (characterised by elimination, not
--                             by what is inside it), so unlike the other
--                             cases below this is a total exception, not
--                             just the binder-crossing half.
--   PiIntro f               — the λ's body: co-data, left alone (same
--                             reason — it's Π's introduction).
--   SigmaTy/Elem.SigmaTy — Γ⊦A (recursed), Γ▷A⊦B (left alone).
--     A B
--   SigmaIntro a b          — Γ⊦a : A, Γ⊦b : B[id,a] — NEITHER crosses a
--                             binder (b's type is already instantiated
--                             at a), so BOTH are recursed into: unlike
--                             the type former, a Σ VALUE is fully data.
--   NatElim z s t           — Γ⊦z, Γ⊦t (recursed), Γ▷ℕ▷A⊦s (left alone).
--   QuotElim f q            — Γ⊦q (recursed), Γ▷A⊦f (left alone).
--   QuotTy/QuotTy A R  — Γ⊦A (recursed), Γ▷A▷A[↑]⊦R (left alone).
--   QSort/QCtor/QElim      — Γ⊦es : the argument/index spine (recursed
--     sg _ es / … es w       — it lives at Γ, no binder); sg itself
--                             (and, for QElim, its motives/methods) is
--                             inherently a bundle of binder telescopes
--                             and is left alone whole; QElim's own
--                             scrutinee w is at Γ (recursed).
--
-- A concrete, testable consequence: nf of `El (a × b)` decodes to
-- `SigmaTy (El a) (El b)` and recurses only into the FIRST component
-- (`El a` fully decodes further; `El b` does not) — contrast a Σ VALUE
-- `(x , y)`, whose SECOND component nf recurses into just as much as
-- the first, since there the binder is already gone (instantiated at
-- x). See Nova.ComputeTest for both, side by side.
--
-- This is also why "stuck on an eliminator" cannot arise while
-- normalizing a closed term: every position nf/whnf ever look at stays,
-- by this same rule applied all the way down, in the ORIGINAL empty
-- context — nothing is ever examined "underneath" a binder that could
-- expose a genuinely unresolved variable. See the next section.
--
-- ===== Closed, well-formed input only =====
--
-- Compute is meant to be run on closed, well-typed terms, never used as
-- a typing/consistency oracle itself. That licenses two simplifications
-- against a more defensive normalizer:
--
--  * el-qiit-beta needs a signature to hand qElimBetaRhs, and there are
--    two candidates in scope at a firing site — the eliminator's own
--    carried signature and the matched constructor's. For a WELL-TYPED
--    eliminator applied to a WELL-TYPED constructor of its own sort,
--    the two necessarily agree on everything the reduction consults
--    (entry shapes, arities), so which one is passed makes no
--    difference; whnf always reduces (no signature comparison at all)
--    and passes the eliminator's own `sg`, arbitrarily.
--
--  * Every elimination site (PiApp, SigmaElim1/2, NatElim, QuotElim,
--    QElim, and El's decoding) whnf's a scrutinee that — BY THE
--    SCRUTINEE'S TYPE, together with the "never under a binder" rule
--    above — can only ever settle into the one matching introduction
--    shape (a function into PiIntro, a pair into SigmaIntro, etc.):
--    since nothing here is ever examined underneath a binder, there is
--    no route to a variable (or an elimination stuck on one) reaching
--    any of these positions in the first place. Any OTHER shape turning
--    up is therefore not a "stuck neutral" to fall through on — it is
--    impossible for a closed, well-typed term, and crashes loudly
--    rather than being silently passed through.

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel.QIIT

%default covering

mutual
  ||| t's weak head normal form.
  export
  whnfElem : Sig -> Elem -> Elem
  whnfElem sig (CtxVar n)         = CtxVar n
  whnfElem sig (ZeroElim t)       = ZeroElim t   -- 𝟘 has no introduction form; never a redex
  whnfElem sig OneIntro           = OneIntro
  whnfElem sig NatIntro0          = NatIntro0
  whnfElem sig (NatIntro1 t)      = NatIntro1 t
  whnfElem sig (NatElim z s t) =
    case whnfElem sig t of
      NatIntro0   => whnfElem sig z
      NatIntro1 n => whnfElem sig (substElem s (Ext (Ext Id n) (NatElim z s n)))
      _ => assert_total $ idris_crash "whnfElem: ℕ-elim scrutinee is not ℕ-shaped (impossible for a closed, well-typed term)"
  whnfElem sig (PiIntro f)        = PiIntro f   -- co-data: canonical, body left alone
  whnfElem sig (PiApp f e) =
    case whnfElem sig f of
      PiIntro g => whnfElem sig (substElem g (Ext Id e))
      _ => assert_total $ idris_crash "whnfElem: application head is not a function (impossible for a closed, well-typed term)"
  -- el-let-beta: a let is ALWAYS a redex
  whnfElem sig (Let a b) = whnfElem sig (substElem b (Ext (Ext Id a) Star))
  whnfElem sig (SigmaIntro a b)   = SigmaIntro a b
  whnfElem sig (SigmaElim1 t) =
    case whnfElem sig t of
      SigmaIntro a _ => whnfElem sig a
      _ => assert_total $ idris_crash "whnfElem: .π₁ scrutinee is not a pair (impossible for a closed, well-typed term)"
  whnfElem sig (SigmaElim2 t) =
    case whnfElem sig t of
      SigmaIntro _ b => whnfElem sig b
      _ => assert_total $ idris_crash "whnfElem: .π₂ scrutinee is not a pair (impossible for a closed, well-typed term)"
  whnfElem sig (Inj1 t)           = Inj1 t
  whnfElem sig (Inj2 t)           = Inj2 t
  whnfElem sig (SumElim l r t) =
    case whnfElem sig t of
      Inj1 a => whnfElem sig (substElem l (Ext Id a))
      Inj2 b => whnfElem sig (substElem r (Ext Id b))
      _ => assert_total $ idris_crash "whnfElem: ⊎-elim scrutinee is not an injection (impossible for a closed, well-typed term)"
  whnfElem sig Elem.ZeroTy        = Elem.ZeroTy
  whnfElem sig Elem.OneTy         = Elem.OneTy
  whnfElem sig Elem.NatTy         = Elem.NatTy
  whnfElem sig UniverseTy         = UniverseTy
  whnfElem sig PropTy             = PropTy
  whnfElem sig TopTy              = TopTy
  whnfElem sig (Elem.PiTy a b)    = Elem.PiTy a b   -- co-data
  whnfElem sig (Elem.SigmaTy a b) = Elem.SigmaTy a b
  whnfElem sig (Elem.SumTy a b)   = Elem.SumTy a b
  whnfElem sig (Elem.EqTy l r t)  = Elem.EqTy l r t
  whnfElem sig (QuotTy a r)       = QuotTy a r
  whnfElem sig (SigVar x es) =
    case sigLookup x sig of
      Just (SigDef _ _ a _) => whnfElem sig (substElem a (embed es))
      -- the evaluator runs over ACCEPTED (definitional) signatures
      -- only; a declaration or wrong-class reference is unreachable
      Just _                => assert_total $ idris_crash "whnfElem: signature identifier '\{x}' is not a term definition (Compute assumes a definitional Σ)"
      Nothing               => assert_total $ idris_crash "whnfElem: signature identifier '\{x}' not found"
  whnfElem sig (Class a)          = Class a
  whnfElem sig (QuotElim f q) =
    case whnfElem sig q of
      Class a => whnfElem sig (substElem f (Ext Id a))
      _ => assert_total $ idris_crash "whnfElem: quot-elim scrutinee is not a class (impossible for a closed, well-typed term)"
  whnfElem sig (Squash t)         =
    case whnfTy sig t of
      p@(Elem.EqTy _ _ _) => p    -- code-squash-idem (syntax-directed
      p@(Squash _)        => p    --   instances; Ω-neutrals stay stuck)
      t'    => Squash t'
  whnfElem sig Star               = Star
  whnfElem sig (Elem.NuTy f)      = Elem.NuTy f
  whnfElem sig (Corec p a f x)    = Corec p a f x   -- co-data: a corec head is canonical
  whnfElem sig (Out t) =
    case whnfElem sig t of
      Corec p a f x => whnfElem sig (mapPoly p (corecCopair p a f) (substElem f (Ext Id x)))
      _ => assert_total $ idris_crash "whnfElem: out scrutinee is not a corec head (impossible for a closed, well-typed term)"
  whnfElem sig (QSort sg k es)   = QSort sg k es
  whnfElem sig (QCtor sg k es)    = QCtor sg k es
  whnfElem sig (QElim sg k ms fs es w) =
    case whnfElem sig w of
      QCtor _ c theta =>   -- either carried signature would do; see the module doc
        case qElimBetaRhs sg ms fs c theta of
          Right rhs => whnfElem sig rhs
          Left err  => assert_total $ idris_crash "whnfElem: el-qiit-beta on an ill-formed eliminator: \{err}"
      _ => assert_total $ idris_crash "whnfElem: QIIT eliminator scrutinee is not a constructor (impossible for a closed, well-typed term)"

  ||| T's weak head normal form — one sort: one evaluator (type
  ||| definitions unfold through the same SigDef clause).
  export
  whnfTy : Sig -> Ty -> Ty
  whnfTy = whnfElem

mutual
  ||| t's normal form: whnf, then nf on every immediate subterm that
  ||| stays in the SAME context — anything living under a binder the
  ||| relevant former introduces (a λ's body, a Π's codomain, a Σ-TYPE's
  ||| second component, ℕ-elim's `s` branch, quot-elim's `f`, a
  ||| quotient's relation, a QIIT signature/motives/methods) is left
  ||| exactly as whnf produced it. See the module doc's "Never under a
  ||| binder" section.
  export
  nfElem : Sig -> Elem -> Elem
  nfElem sig e0 = go (whnfElem sig e0)
   where
    go : Elem -> Elem
    go (CtxVar n)         = CtxVar n
    go (ZeroElim t)       = ZeroElim (nfElem sig t)
    go OneIntro           = OneIntro
    go NatIntro0          = NatIntro0
    go (NatIntro1 t)      = NatIntro1 (nfElem sig t)
    go (NatElim z s t)    = NatElim (nfElem sig z) s (nfElem sig t)   -- s: under a binder, left alone
    go (PiIntro f)        = PiIntro f   -- co-data: leave the body
    go (PiApp f e)        = PiApp (nfElem sig f) (nfElem sig e)
    go (SigmaIntro a b)   = SigmaIntro (nfElem sig a) (nfElem sig b)   -- a Σ VALUE: no binder crossed
    go (SigmaElim1 t)     = SigmaElim1 (nfElem sig t)
    go (SigmaElim2 t)     = SigmaElim2 (nfElem sig t)
    go (Inj1 t)           = Inj1 (nfElem sig t)   -- an injection is data: no binder crossed
    go (Inj2 t)           = Inj2 (nfElem sig t)
    go (SumElim l r t)    = SumElim l r (nfElem sig t)   -- l, r: under a binder, left alone
    go Elem.ZeroTy        = Elem.ZeroTy
    go Elem.OneTy         = Elem.OneTy
    go Elem.NatTy         = Elem.NatTy
    go UniverseTy         = UniverseTy
    go PropTy             = PropTy
    go TopTy              = TopTy
    go (Elem.PiTy a b)    = Elem.PiTy a b   -- co-data: leave domain/codomain
    go (Elem.SigmaTy a b) = Elem.SigmaTy (nfElem sig a) b   -- b: under a binder, left alone
    go (Elem.SumTy a b)   = Elem.SumTy (nfElem sig a) (nfElem sig b)   -- non-dependent: BOTH recursed
    go (Elem.EqTy l r t)  = Elem.EqTy (nfElem sig l) (nfElem sig r) (nfTy sig t)
    go (QuotTy a r)       = QuotTy (nfElem sig a) r   -- r: under a binder, left alone
    go (SigVar x es)      = SigVar x es   -- unreachable: whnf always unfolds x[e˲]
    go (Let a b)          = Let a b   -- unreachable: whnf always contracts a let
    go (Class a)          = Class (nfElem sig a)
    go (QuotElim f q)     = QuotElim f (nfElem sig q)   -- f: under a binder, left alone
    go (Squash t)         =
      case nfTy sig t of
        p@(Elem.EqTy _ _ _) => p  -- code-squash-idem instances
        p@(Squash _)        => p
        t'    => Squash t'
    go Star               = Star
    go (QSort sg k es)   = QSort sg k (nfSubNorm sig es)   -- sg: a bundle of binder telescopes, left alone
    go (QCtor sg k es)    = QCtor sg k (nfSubNorm sig es)
    go (QElim sg k ms fs es w) = QElim sg k ms fs (nfSubNorm sig es) (nfElem sig w)
    go (Elem.NuTy f)      = Elem.NuTy f   -- 𝔽: embedded pieces partly under binders, left alone
    go (Out t)            = Out (nfElem sig t)
    go (Corec p a f x)    = Corec p (nfElem sig a) f (nfElem sig x)   -- f: under a binder, left alone

  ||| T's normal form — one sort: one normalizer.
  export
  nfTy : Sig -> Ty -> Ty
  nfTy = nfElem

  export
  nfSubNorm : Sig -> SubNorm -> SubNorm
  nfSubNorm sig [<] = [<]
  nfSubNorm sig (es :< e) = nfSubNorm sig es :< nfElem sig e
