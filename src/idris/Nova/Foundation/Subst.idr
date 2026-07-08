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
  ||| Γ‖ₙ-style variable resolution against a concrete substitution:
  ||| what (☐ₙ)[σ] computes to.
  export
  substVar : Sub -> Nat -> Elem
  -- Terminal's codomain is ε, which has no variables, so ☐ₙ can never be
  -- well-typed there — crash loudly instead of fabricating a result.
  substVar Terminal      n     = assert_total $ idris_crash "substVar: ill-typed ☐\{show n} against · (empty codomain)"
  substVar Id            n     = CtxVar n
  substVar Wk             n     = CtxVar (S n)
  substVar (Ext sigma t) Z     = t
  substVar (Ext sigma t) (S n) = substVar sigma n
  substVar (Chain s t)   n     = substElem t (substVar s n)

  export
  substElem : Sub -> Elem -> Elem
  substElem sigma (SubstElim e tau)      = substElem sigma (substElem tau e)
  substElem sigma (CtxVar n)             = substVar sigma n
  substElem sigma (ZeroElim t)           = ZeroElim (substElem sigma t)
  substElem sigma OneIntro               = OneIntro
  substElem sigma NatIntro0              = NatIntro0
  substElem sigma (NatIntro1 t)          = NatIntro1 (substElem sigma t)
  substElem sigma (NatElim z s t)        = NatElim (substElem sigma z) (substElem (under (under sigma)) s) (substElem sigma t)
  substElem sigma (PiIntro f)            = PiIntro (substElem (under sigma) f)
  substElem sigma (PiApp f e)            = PiApp (substElem sigma f) (substElem sigma e)
  substElem sigma (SigmaIntro a b)       = SigmaIntro (substElem sigma a) (substElem sigma b)
  substElem sigma (SigmaElim1 t)         = SigmaElim1 (substElem sigma t)
  substElem sigma (SigmaElim2 t)         = SigmaElim2 (substElem sigma t)
  substElem sigma Elem.ZeroTy            = Elem.ZeroTy
  substElem sigma Elem.OneTy             = Elem.OneTy
  substElem sigma Elem.NatTy             = Elem.NatTy
  substElem sigma (Elem.PiTy a b)        = Elem.PiTy (substElem sigma a) (substElem (under sigma) b)
  substElem sigma (Elem.SigmaTy a b)     = Elem.SigmaTy (substElem sigma a) (substElem (under sigma) b)
  substElem sigma (Elem.EqTy l r t)      = Elem.EqTy (substElem sigma l) (substElem sigma r) (substElem sigma t)
  substElem sigma Refl                   = Refl
  substElem sigma (SigVar x)             = SigVar x

export
substTy : Sub -> Ty -> Ty
substTy sigma (Ty.SubstElim ty tau) = substTy sigma (substTy tau ty)
substTy sigma Ty.ZeroTy             = Ty.ZeroTy
substTy sigma Ty.OneTy              = Ty.OneTy
substTy sigma Ty.NatTy              = Ty.NatTy
substTy sigma Ty.UniverseTy         = Ty.UniverseTy
substTy sigma (Ty.PiTy a b)         = Ty.PiTy (substTy sigma a) (substTy (under sigma) b)
substTy sigma (Ty.SigmaTy a b)      = Ty.SigmaTy (substTy sigma a) (substTy (under sigma) b)
substTy sigma (EqTy l r ty)         = EqTy (substElem sigma l) (substElem sigma r) (substTy sigma ty)
substTy sigma (El e)                = El (substElem sigma e)

export
substTel : Sub -> Tel -> Tel
substTel sigma []          = []
substTel sigma (ty :: rest) = substTy sigma ty :: substTel (under sigma) rest

export
substSpine : Sub -> Spine -> Spine
substSpine sigma []        = []
substSpine sigma (e :: es) = substElem sigma e :: substSpine sigma es
