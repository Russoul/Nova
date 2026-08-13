||| Judgment-carrying elaboration: the working state
||| (docs/NovaPipeline.txt, "Phase 3 end-state, revised").
|||
||| A Jud is a DERIVATION paired with its cached erasure — the
||| context, spelling, and type the elaborator would otherwise carry
||| bare. The derivation is untrusted data (the seat erases and
||| replays through conclude, which remains the sole authority), so
||| these constructors perform NO side-condition checks: the
||| elaborator is the producer and writes down what it built; a wrong
||| move surfaces as a seat rejection, exactly as today, never as an
||| acceptance. What the constructors DO guarantee is the structural
||| invariant the whole design rests on: no spelling travels without
||| its derivation, so premise access is projection — reading a field
||| of a Jud in hand — never inversion.
|||
||| Migration (strangler-fig, docs/NovaPipeline.txt): elaboration
||| routes port to Jud-valued form one at a time; unported routes
||| keep returning bare spellings and the emission pass
||| (Nova.Kernel.Reconstruct) remains their adapter. This module is
||| the seed: the judgment forms, their erasures, and the
||| constructors the ⋆-discharge pilot needs. It grows with the port
||| and is consumed by nothing yet.
module Nova.Elaboration.Jud

import Data.SnocList

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel.Beta
import Nova.Kernel.Derivation

-- substitution and contraction reach the kernel's fuel-free walkers,
-- which Idris cannot see terminating; totality is not this module's
-- claim to make
%default covering

||| Γ ⊦ t : A, with the derivation.
public export
record Jud where
  constructor MkJud
  deriv : Deriv
  ctx : Ctx
  elem : Elem
  ty : Ty

||| Γ ⊦ A type, with the derivation.
public export
record JudTy where
  constructor MkJudTy
  deriv : Deriv
  ctx : Ctx
  ty : Ty

||| Γ ⊦ t₀ ≐ t₁ : A, with the derivation.
public export
record JudEq where
  constructor MkJudEq
  deriv : Deriv
  ctx : Ctx
  lhs : Elem
  rhs : Elem
  ty : Ty

||| Γ ⊦ A₀ ≐ A₁ type, with the derivation.
public export
record JudTyEq where
  constructor MkJudTyEq
  deriv : Deriv
  ctx : Ctx
  lhs : Ty
  rhs : Ty

-- ===== structural rules =====

wkTy : Nat -> Ty -> Ty
wkTy Z t = t
wkTy (S n) t = wkTy n (substTy t Wk)

||| ☐ᵢ at its context-assigned type (el-var).
export
judVar : Ctx -> Nat -> Maybe Jud
judVar cx i = do
  t <- go (toList (reverse cx)) i
  pure (MkJud (DElVar i) cx (CtxVar i) (wkTy (S i) t))
 where
  go : List Ty -> Nat -> Maybe Ty
  go [] _ = Nothing
  go (t :: _) Z = Just t
  go (_ :: rest) (S n) = go rest n

||| λ-introduction (el-pi-i): the domain's formation and the body's
||| judgment in the extended context.
export
judPiI : JudTy -> Jud -> Jud
judPiI dom body =
  MkJud (DElPiI dom.deriv body.deriv) dom.ctx
    (PiIntro body.elem) (Ty.PiTy dom.ty body.ty)

||| Application (el-pi-e): the function at a Π, the argument at its
||| domain, the codomain's formation in the extended context. The
||| producer asserts the domain fit; the seat checks it.
export
judPiE : Jud -> Jud -> JudTy -> Maybe Jud
judPiE f e cod = do
  let Ty.PiTy _ b = f.ty
    | _ => Nothing
  pure (MkJud (DElPiE f.deriv e.deriv cod.deriv) f.ctx
          (PiApp f.elem e.elem) (substTy b (Ext Id e.elem)))

||| Coercion along a type equation (el-ty-coe).
export
judCoe : JudTyEq -> Jud -> Jud
judCoe eq j = MkJud (DElTyCoe eq.deriv j.deriv) j.ctx j.elem eq.rhs

-- ===== introductions and references =====

export
judZero : Ctx -> Jud
judZero cx = MkJud DElNatZ cx NatIntro0 Ty.NatTy

export
judSuc : Jud -> Jud
judSuc j = MkJud (DElNatS j.deriv) j.ctx (NatIntro1 j.elem) Ty.NatTy

export
judOneI : Ctx -> Jud
judOneI cx = MkJud DElOneI cx OneIntro Ty.OneTy

||| A closed signature reference (empty declaration context): el-sig
||| at the empty spine. The cached type is spelled as conclude spells
||| it — the closed type substituted along the empty embedding.
export
judSig0 : SigIdentifier -> Ty -> Ctx -> Jud
judSig0 x a cx =
  MkJud (DElSig x DSubNEmpty) cx (Elem.SigVar x [<]) (substTy a Terminal)

export
judTyNat : Ctx -> JudTy
judTyNat cx = MkJudTy DTyNat cx Ty.NatTy

||| The nullary formations, written down directly.
export
judTyPrim : Ctx -> Ty -> Maybe JudTy
judTyPrim cx Ty.NatTy = Just (MkJudTy DTyNat cx Ty.NatTy)
judTyPrim cx Ty.OneTy = Just (MkJudTy DTyOne cx Ty.OneTy)
judTyPrim cx Ty.ZeroTy = Just (MkJudTy DTyZero cx Ty.ZeroTy)
judTyPrim cx Ty.UniverseTy = Just (MkJudTy DTyUniv cx Ty.UniverseTy)
judTyPrim cx Ty.PropTy = Just (MkJudTy DTyProp cx Ty.PropTy)
judTyPrim _ _ = Nothing

||| A formation substituted along a substitution DERIVATION
||| (ty-sub-cong-fix at refl, presupposed): one wrap; conclude
||| computes the substituted spelling eagerly, and the caller caches
||| the same spelling.
export
judSubTy : Deriv -> Ctx -> Ty -> JudTy -> JudTy
judSubTy dS cx sp ft =
  MkJudTy (DPresupTyL (DTySubCongFix dS (DTyRefl ft.deriv))) cx sp

||| ℕ-elimination (el-nat-e): the motive's formation over ctx▷ℕ and
||| the three premises, each at its motive instance.
export
judNatE : JudTy -> Jud -> Jud -> Jud -> Jud
judNatE mot z s t =
  MkJud (DElNatE mot.deriv z.deriv s.deriv t.deriv) t.ctx
    (NatElim z.elem s.elem t.elem) (substTy mot.ty (Ext Id t.elem))

-- ===== type formations by construction =====

export
judTyPrf : Jud -> JudTy
judTyPrf p = MkJudTy (DTyPrf p.deriv) p.ctx (Prf p.elem)

export
judTyEl : Jud -> JudTy
judTyEl a = MkJudTy (DTyEl a.deriv) a.ctx (El a.elem)

export
judTyPi : JudTy -> JudTy -> JudTy
judTyPi a b = MkJudTy (DTyPi a.deriv b.deriv) a.ctx (Ty.PiTy a.ty b.ty)

export
judTySigma : JudTy -> JudTy -> JudTy
judTySigma a b = MkJudTy (DTySigma a.deriv b.deriv) a.ctx (Ty.SigmaTy a.ty b.ty)

||| The equality PROPOSITION's code (code-eq): the ambient type's
||| formation and the two sides at it.
export
judCodeEq : JudTy -> Jud -> Jud -> Jud
judCodeEq t l r =
  MkJud (DCodeEq t.deriv l.deriv r.deriv) t.ctx
    (Elem.EqTy l.elem r.elem t.ty) Ty.PropTy

-- ===== formation projections =====
-- The domain and codomain formations behind a function's Π, read by
-- presupposition + inversion — one node each, deterministic, never
-- reconstructed. The spellings are the caller's (it exposed the Π).

export
judInvPiDom : Jud -> Ty -> JudTy
judInvPiDom f a = MkJudTy (DInvPiDom (DPresupElTy f.deriv)) f.ctx a

export
judInvPiCod : Jud -> Ty -> Ty -> JudTy
judInvPiCod f a b = MkJudTy (DInvPiCod (DPresupElTy f.deriv)) (f.ctx :< a) b

-- ===== equational rules =====

export
judRefl : Jud -> JudEq
judRefl j = MkJudEq (DElRefl j.deriv) j.ctx j.elem j.elem j.ty

export
judSym : JudEq -> JudEq
judSym e = MkJudEq (DElSym e.deriv) e.ctx e.rhs e.lhs e.ty

||| Transitivity; the producer asserts the middles meet.
export
judTrans : JudEq -> JudEq -> JudEq
judTrans a b = MkJudEq (DElTrans a.deriv b.deriv) a.ctx a.lhs b.rhs a.ty

||| One ≜ contraction at a path (beta-at): the exposure link. The
||| contraction is computed here — the one place a constructor does
||| work — because the conclusion's spelling IS its result.
export
judBetaAt : Sig -> List Nat -> Jud -> Maybe JudEq
judBetaAt sig p j = do
  t' <- contractAtE sig p j.elem
  pure (MkJudEq (DBetaAt p j.deriv) j.ctx j.elem t' j.ty)

-- ===== presupposition projection =====
-- The design's central dividend: the typing of a spelling in hand is
-- a field read plus one node, never a re-derivation.

export
judEqLhs : JudEq -> Jud
judEqLhs e = MkJud (DPresupElL e.deriv) e.ctx e.lhs e.ty

export
judEqRhs : JudEq -> Jud
judEqRhs e = MkJud (DPresupElR e.deriv) e.ctx e.rhs e.ty

export
judElTy : Jud -> JudTy
judElTy j = MkJudTy (DPresupElTy j.deriv) j.ctx j.ty
