module Nova.Core.Occurrence

import Data.AVL

import Nova.Control.Monad.Id

import Nova.Core.Substitution
import Nova.Core.Evaluation
import Nova.Core.Language

mutual
  namespace SubstContextNF
    public export
    freeOmegaName : Signature -> Omega -> SubstContextNF -> EvalM (Set OmegaName)
    freeOmegaName sig omega Terminal = Id.pure empty
    freeOmegaName sig omega (WkN j) = Id.pure empty
    freeOmegaName sig omega (Ext sigma t) = Id.do
      [| unite (freeOmegaName sig omega sigma) (freeOmegaName sig omega t) |]

  namespace SubstContext
    public export
    freeOmegaName : Signature -> Omega -> SubstContext -> EvalM (Set OmegaName)
    freeOmegaName sig omega sigma = freeOmegaName sig omega (eval sigma)

  namespace Typ
    public export
    freeOmegaNameNu : Signature -> Omega -> Typ -> EvalM (Set OmegaName)
    freeOmegaNameNu sig omega (PiTy x dom cod) = Id.do
      [| unite (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) |]
    freeOmegaNameNu sig omega (ImplicitPiTy x dom cod) = Id.do
      [| unite (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) |]
    freeOmegaNameNu sig omega (SigmaTy x dom cod) = Id.do
      [| unite (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) |]
    freeOmegaNameNu sig omega NatTy = pure empty
    freeOmegaNameNu sig omega ZeroTy = pure empty
    freeOmegaNameNu sig omega OneTy = pure empty
    freeOmegaNameNu sig omega UniverseTy = pure empty
    freeOmegaNameNu sig omega (El a) = freeOmegaName sig omega a
    freeOmegaNameNu sig omega (ContextSubstElim x y) = assert_total $ idris_crash "freeOmegaNameNu(ContextSubstElim)"
    freeOmegaNameNu sig omega (SignatureSubstElim x y) = assert_total $ idris_crash "freeOmegaNameNu(SignatureSubstElim)"
    freeOmegaNameNu sig omega (OmegaVarElim j sigma) = Id.do
      sigma <- freeOmegaName sig omega sigma
      pure (insert j sigma)
    freeOmegaNameNu sig omega (TyEqTy a b) = Id.do
      [| unite (freeOmegaName sig omega a) (freeOmegaName sig omega b) |]
    freeOmegaNameNu sig omega (ElEqTy a b ty) = Id.do
      [| unite3 (freeOmegaName sig omega a) (freeOmegaName sig omega b) (freeOmegaName sig omega ty) |]
    freeOmegaNameNu sig omega (SignatureVarElim j sigma) = freeOmegaName sig omega sigma

    ||| Compute free occurrences of Ω variables in the term modulo open evaluation.
    public export
    freeOmegaName : Signature -> Omega -> Typ -> EvalM (Set OmegaName)
    freeOmegaName sig omega t = freeOmegaNameNu sig omega !(openEval sig omega t)

  namespace Elem
    public export
    freeOmegaNameNu : Signature -> Omega -> Elem -> EvalM (Set OmegaName)
    freeOmegaNameNu sig omega (PiTy x dom cod) = Id.do
      [| unite (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) |]
    freeOmegaNameNu sig omega (ImplicitPiTy x dom cod) = Id.do
      [| unite (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) |]
    freeOmegaNameNu sig omega (SigmaTy x dom cod) = Id.do
      [| unite (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) |]
    freeOmegaNameNu sig omega (PiVal x dom cod f) = Id.do
      [| unite3 (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) (freeOmegaName sig omega f) |]
    freeOmegaNameNu sig omega (ImplicitPiVal x dom cod f) =
      [| unite3 (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) (freeOmegaName sig omega f) |]
    freeOmegaNameNu sig omega (SigmaVal x a b p q) = Id.do
      [| unite4 (freeOmegaName sig omega a) (freeOmegaName sig omega b) (freeOmegaName sig omega p) (freeOmegaName sig omega q) |]
    freeOmegaNameNu sig omega (PiElim f x dom cod e) = Id.do
      [|
         unite4 (freeOmegaName sig omega f)
                (freeOmegaName sig omega dom)
                (freeOmegaName sig omega cod)
                (freeOmegaName sig omega e)
      |]
    freeOmegaNameNu sig omega (ImplicitPiElim f x dom cod e) = Id.do
      [|
         unite4 (freeOmegaName sig omega f)
                (freeOmegaName sig omega dom)
                (freeOmegaName sig omega cod)
                (freeOmegaName sig omega e)
      |]
    freeOmegaNameNu sig omega (SigmaElim1 f x dom cod) = Id.do
      [| unite3 (freeOmegaName sig omega f) (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) |]
    freeOmegaNameNu sig omega (SigmaElim2 f x dom cod) = Id.do
      [| unite3 (freeOmegaName sig omega f) (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) |]
    freeOmegaNameNu sig omega NatVal0 = pure empty
    freeOmegaNameNu sig omega (NatVal1 t) = freeOmegaName sig omega t
    freeOmegaNameNu sig omega NatTy = pure empty
    freeOmegaNameNu sig omega ZeroTy = pure empty
    freeOmegaNameNu sig omega OneTy = pure empty
    freeOmegaNameNu sig omega OneVal = pure empty
    freeOmegaNameNu sig omega (ZeroElim ty t) = Id.do
      [| unite (freeOmegaName sig omega ty) (freeOmegaName sig omega t) |]
    freeOmegaNameNu sig omega (NatElim x schema z y h s t) = Id.do
      [| unite4
           (freeOmegaName sig omega schema)
           (freeOmegaName sig omega z)
           (freeOmegaName sig omega s)
           (freeOmegaName sig omega t)
      |]
    freeOmegaNameNu sig omega (ContextSubstElim x y) = assert_total $ idris_crash "freeOmegaNameNu(ContextSubstElim)"
    freeOmegaNameNu sig omega (SignatureSubstElim x y) = assert_total $ idris_crash "freeOmegaNameNu(SignatureSubstElim)"
    freeOmegaNameNu sig omega (ContextVarElim j) = pure empty
    freeOmegaNameNu sig omega (SignatureVarElim j sigma) = freeOmegaName sig omega sigma
    freeOmegaNameNu sig omega (OmegaVarElim j sigma) = Id.do
      sigma <- freeOmegaName sig omega sigma
      pure (insert j sigma)
    freeOmegaNameNu sig omega (TyEqTy a b) = Id.do
      [| unite (freeOmegaName sig omega a) (freeOmegaName sig omega b) |]
    freeOmegaNameNu sig omega (ElEqTy a b ty) = Id.do
      [| unite3 (freeOmegaName sig omega a) (freeOmegaName sig omega b) (freeOmegaName sig omega ty) |]
    freeOmegaNameNu sig omega (TyEqVal ty) = freeOmegaName sig omega ty
    freeOmegaNameNu sig omega (ElEqVal ty e) = Id.do
      [| unite (freeOmegaName sig omega ty) (freeOmegaName sig omega e) |]

    ||| Compute free occurrences of Ω variables in the term modulo open evaluation.
    public export
    freeOmegaName : Signature -> Omega -> Elem -> EvalM (Set OmegaName)
    freeOmegaName sig omega t = freeOmegaNameNu sig omega !(openEval sig omega t)

namespace Context
  public export
  freeOmegaName : Signature -> Omega -> Context -> EvalM (Set OmegaName)
  freeOmegaName sig omega [<] = pure empty
  freeOmegaName sig omega (ctx :< (x, ty)) = Id.do
    [| unite (freeOmegaName sig omega ctx) (freeOmegaName sig omega ty) |]

