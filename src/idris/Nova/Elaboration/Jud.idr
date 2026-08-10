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
