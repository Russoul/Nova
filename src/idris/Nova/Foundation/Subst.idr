module Nova.Foundation.Subst

-- A direct, structurally-recursive substitution algorithm for Ty/Elem/Tel/
-- Spine, matching the "by definition" (≜) substitution equations in
-- docs/NovaFoundation.txt, rather than the ComputeRule-based one-step-at-a-
-- time reduction relation in Derivation.idr's computeTy/computeElem.
--
-- Unlike ComputeRule (which only ever makes one step of progress and can
-- get stuck with "no rule applies"), this always fully computes A[σ]/t[σ]
-- in one call — for any Ty/Elem/Tel/Spine and any concrete σ, since Sub's
-- constructors (Terminal/Ext/Chain/Id/Wk) are always finitely resolvable.
-- It also eagerly resolves any SubstElim already embedded in the input
-- term, so it never leaves a pending substitution behind in its result.
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

import Nova.Foundation.Syntax

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
  substElem Refl               sigma = Refl
  substElem (SigVar x es)      sigma = SigVar x (substSubNorm es sigma)
  substElem (Class a)          sigma = Class (substElem a sigma)
  substElem (QuotElim f q)     sigma = QuotElim (substElem f (under sigma)) (substElem q sigma)

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
substTy (Quotient a r)        sigma = Quotient (substTy a sigma) (substTy r (under (under sigma)))

||| Δ[σ]
export
substTel : Tel -> Sub -> Tel
substTel []           sigma = []
substTel (ty :: rest) sigma = substTy ty sigma :: substTel rest (under sigma)

||| ē[σ]
export
substSpine : Spine -> Sub -> Spine
substSpine []        sigma = []
substSpine (e :: es) sigma = substElem e sigma :: substSpine es sigma

export
embed : SubNorm -> Sub
embed [<] = Terminal
embed (es :< e) = Ext (embed es) e
