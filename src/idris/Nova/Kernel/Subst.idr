module Nova.Kernel.Subst

-- A direct, structurally-recursive substitution algorithm for Ty/Elem,
-- matching the "by definition" (≜) substitution equations in
-- docs/NovaFoundation.txt.
--
-- This always fully computes A[σ]/t[σ] in one call — for any Ty/Elem
-- and any concrete σ, since Sub's constructors (Terminal/Ext/Chain/
-- Id/Wk) are always finitely resolvable. It also eagerly resolves any
-- SubstElim already embedded in the input term, so it never leaves a
-- pending substitution behind in its result.
--
-- Argument order matches Syntax.idr's SubstElim (object first, then the
-- substitution): substElem t sigma computes t[σ].
--
-- Composition convention: `Chain s t` prints as "s ∘ t" and behaves like
-- ordinary function composition — s is applied first (to the original
-- term), t second (to s's result) — i.e. `x[Chain s t] = x[s][t]`. This
-- matches the existing (tested) computeSub rule
-- `Chain Wk (Ext sigma _) -> sigma` ("↑ ∘ (σ, e) = σ": weakening
-- immediately cancels a just-added extension) and Syntax.under's
-- `Ext (Chain sigma Wk) (CtxVar 0)` ("σ⁺ = σ ∘ ↑, ☐₀").
--
-- Not wired into the checker yet — this module is standalone.

import Nova.Kernel.Syntax

%default covering

mutual
  ||| e˲[σ]
  export
  substSubNorm : SubNorm -> Sub -> SubNorm
  substSubNorm [<] sigma = [<]
  substSubNorm (es :< e) sigma = substSubNorm es sigma :< substElem e sigma

  ||| Γ‖ₙ-style variable resolution against a concrete substitution:
  ||| what (☐ₙ)[σ] computes to.
  export
  substVar : Nat -> Sub -> Elem
  -- Terminal's codomain is ε, which has no variables, so ☐ₙ can never be
  -- well-typed there — crash loudly instead of fabricating a result.
  substVar n     Terminal    = assert_total $ idris_crash "substVar: ill-typed ☐\{show n} against · (empty codomain)"
  substVar n     Id          = CtxVar n
  substVar n     Wk          = CtxVar (S n)
  substVar Z     (Ext sigma t) = t
  substVar (S n) (Ext sigma t) = substVar n sigma
  substVar n     (Chain s t) = substElem (substVar n s) t

  ||| t[σ]
  export
  substElem : Elem -> Sub -> Elem
  substElem (CtxVar n)         sigma = substVar n sigma
  substElem (ZeroElim t)       sigma = ZeroElim (substElem t sigma)
  substElem OneIntro           sigma = OneIntro
  substElem NatIntro0          sigma = NatIntro0
  substElem (NatIntro1 t)      sigma = NatIntro1 (substElem t sigma)
  substElem (NatElim z s t)    sigma = NatElim (substElem z sigma) (substElem s (under (under sigma))) (substElem t sigma)
  substElem (PiIntro f)        sigma = PiIntro (substElem f (under sigma))
  substElem (PiApp f e)        sigma = PiApp (substElem f sigma) (substElem e sigma)
  substElem (SigmaIntro a b)   sigma = SigmaIntro (substElem a sigma) (substElem b sigma)
  substElem (SigmaElim1 t)     sigma = SigmaElim1 (substElem t sigma)
  substElem (SigmaElim2 t)     sigma = SigmaElim2 (substElem t sigma)
  substElem Elem.ZeroTy        sigma = Elem.ZeroTy
  substElem Elem.OneTy         sigma = Elem.OneTy
  substElem Elem.NatTy         sigma = Elem.NatTy
  substElem (Elem.PiTy a b)    sigma = Elem.PiTy (substElem a sigma) (substElem b (under sigma))
  substElem (Elem.SigmaTy a b) sigma = Elem.SigmaTy (substElem a sigma) (substElem b (under sigma))
  substElem (Elem.EqTy l r t)  sigma = Elem.EqTy (substElem l sigma) (substElem r sigma) (substElem t sigma)
  substElem (QuotTy a r)       sigma = QuotTy (substElem a sigma) (substElem r (under (under sigma)))
  substElem Refl               sigma = Refl
  substElem (SigVar x es)      sigma = SigVar x (substSubNorm es sigma)
  substElem (Class a)          sigma = Class (substElem a sigma)
  substElem (QuotElim f q)     sigma = QuotElim (substElem f (under sigma)) (substElem q sigma)
  substElem (Squash t)         sigma = Squash (substTy t sigma)
  substElem Star               sigma = Star

  ||| T[σ]
  export
  substTy : Ty -> Sub -> Ty
  substTy Ty.ZeroTy             sigma = Ty.ZeroTy
  substTy Ty.OneTy              sigma = Ty.OneTy
  substTy Ty.NatTy              sigma = Ty.NatTy
  substTy Ty.UniverseTy         sigma = Ty.UniverseTy
  substTy (Ty.PiTy a b)         sigma = Ty.PiTy (substTy a sigma) (substTy b (under sigma))
  substTy (Ty.SigmaTy a b)      sigma = Ty.SigmaTy (substTy a sigma) (substTy b (under sigma))
  substTy (EqTy l r ty)         sigma = EqTy (substElem l sigma) (substElem r sigma) (substTy ty sigma)
  substTy (El e)                sigma = El (substElem e sigma)
  substTy PropTy                sigma = PropTy
  substTy (Prf e)               sigma = Prf (substElem e sigma)
  substTy (Quotient a r)        sigma = Quotient (substTy a sigma) (substElem r (under (under sigma)))
  substTy (Ty.SigVar x es)      sigma = Ty.SigVar x (substSubNorm es sigma)



export
embed : SubNorm -> Sub
embed [<] = Terminal
embed (es :< e) = Ext (embed es) e

-- ===== Strengthening (partial inverse of weakening by ↑) =====
--
-- strengthenXxx d x undoes one weakening step: it succeeds exactly when x
-- never references the variable at de Bruijn depth d (i.e. x is in the
-- image of ↑ under d local binders), returning x with every free index
-- above d decremented. Binder bookkeeping mirrors substXxx exactly. Used
-- by the elaborator's candidate canonicalization; call with d = 0.
--
-- NOTE: strengthening is a raw syntactic operation — index arithmetic
-- only. Its output is NOT necessarily well-formed (nothing here consults
-- a context or the signature), and success does NOT mean the input was
-- derivable one binder up: it only means the input is syntactically in
-- the image of ↑. Callers must never treat a strengthened result as a
-- judgement — the elaborator uses it only to canonicalize candidate
-- patterns, and anything it produces is re-established by the kernel.

mutual
  export
  strengthenElem : (depth : Nat) -> Elem -> Maybe Elem
  strengthenElem d (CtxVar n) =
    if n < d then Just (CtxVar n)
    else if n == d then Nothing
    else Just (CtxVar (minus n 1))
  strengthenElem d (ZeroElim t)       = ZeroElim <$> strengthenElem d t
  strengthenElem d OneIntro           = Just OneIntro
  strengthenElem d NatIntro0          = Just NatIntro0
  strengthenElem d (NatIntro1 t)      = NatIntro1 <$> strengthenElem d t
  strengthenElem d (NatElim z s t)    = NatElim <$> strengthenElem d z <*> strengthenElem (2 + d) s <*> strengthenElem d t
  strengthenElem d (PiIntro f)        = PiIntro <$> strengthenElem (1 + d) f
  strengthenElem d (PiApp f e)        = PiApp <$> strengthenElem d f <*> strengthenElem d e
  strengthenElem d (SigmaIntro a b)   = SigmaIntro <$> strengthenElem d a <*> strengthenElem d b
  strengthenElem d (SigmaElim1 t)     = SigmaElim1 <$> strengthenElem d t
  strengthenElem d (SigmaElim2 t)     = SigmaElim2 <$> strengthenElem d t
  strengthenElem d Elem.ZeroTy        = Just Elem.ZeroTy
  strengthenElem d Elem.OneTy         = Just Elem.OneTy
  strengthenElem d Elem.NatTy         = Just Elem.NatTy
  strengthenElem d (Elem.PiTy a b)    = Elem.PiTy <$> strengthenElem d a <*> strengthenElem (1 + d) b
  strengthenElem d (Elem.SigmaTy a b) = Elem.SigmaTy <$> strengthenElem d a <*> strengthenElem (1 + d) b
  strengthenElem d (Elem.EqTy l r t)  = Elem.EqTy <$> strengthenElem d l <*> strengthenElem d r <*> strengthenElem d t
  strengthenElem d (QuotTy a r)       = QuotTy <$> strengthenElem d a <*> strengthenElem (2 + d) r
  strengthenElem d Refl               = Just Refl
  strengthenElem d (SigVar x es)      = SigVar x <$> strengthenSubNorm d es
  strengthenElem d (Class a)          = Class <$> strengthenElem d a
  strengthenElem d (QuotElim f q)     = QuotElim <$> strengthenElem (1 + d) f <*> strengthenElem d q
  strengthenElem d (Squash t)         = Squash <$> strengthenTy d t
  strengthenElem d Star               = Just Star

  export
  strengthenSubNorm : (depth : Nat) -> SubNorm -> Maybe SubNorm
  strengthenSubNorm d [<] = Just [<]
  strengthenSubNorm d (es :< e) = (:<) <$> strengthenSubNorm d es <*> strengthenElem d e

  export
  strengthenTy : (depth : Nat) -> Ty -> Maybe Ty
  strengthenTy d Ty.ZeroTy         = Just Ty.ZeroTy
  strengthenTy d Ty.OneTy          = Just Ty.OneTy
  strengthenTy d Ty.NatTy          = Just Ty.NatTy
  strengthenTy d Ty.UniverseTy     = Just Ty.UniverseTy
  strengthenTy d (Ty.PiTy a b)     = Ty.PiTy <$> strengthenTy d a <*> strengthenTy (1 + d) b
  strengthenTy d (Ty.SigmaTy a b)  = Ty.SigmaTy <$> strengthenTy d a <*> strengthenTy (1 + d) b
  strengthenTy d (EqTy l r ty)     = EqTy <$> strengthenElem d l <*> strengthenElem d r <*> strengthenTy d ty
  strengthenTy d (El e)            = El <$> strengthenElem d e
  strengthenTy d PropTy            = Just PropTy
  strengthenTy d (Prf e)           = Prf <$> strengthenElem d e
  strengthenTy d (Quotient a r)    = Quotient <$> strengthenTy d a <*> strengthenElem (2 + d) r
  strengthenTy d (Ty.SigVar x es)  = Ty.SigVar x <$> strengthenSubNorm d es

||| Only surface-shaped substitutions (flat Ext/Terminal element lists)
||| strengthen; Id/Wk/Chain are index-sensitive and never appear in
||| queries, so they conservatively fail.
export
strengthenSub : (depth : Nat) -> Sub -> Maybe Sub
strengthenSub d Terminal  = Just Terminal
strengthenSub d (Ext s e) = Ext <$> strengthenSub d s <*> strengthenElem d e
strengthenSub d _         = Nothing



||| σ elementwise-weakened by ↑ — how the same (surface, Ext/Terminal)
||| substitution is spelled one binder up in its domain (σ ∘ ↑, by the
||| extension-postcomposition rule). Id/Wk/Chain are unreachable here
||| (strengthenSub never produces them) — crash loudly rather than
||| fabricate a result.
export
weakenSub : Sub -> Sub
weakenSub Terminal  = Terminal
weakenSub (Ext s e) = Ext (weakenSub s) (substElem e Wk)
weakenSub s         = assert_total $ idris_crash "weakenSub: non-surface substitution"
