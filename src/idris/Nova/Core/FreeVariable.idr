module Nova.Core.FreeVariable

import Data.AVL

import Nova.Core.Monad
import Nova.Core.Substitution
import Nova.Core.Evaluation
import Nova.Core.Language

mutual
  namespace SubstContextNF
    public export
    freeOmegaName : Signature -> Omega -> SubstContextNF -> M (Set OmegaName)
    freeOmegaName sig omega Terminal = return empty
    freeOmegaName sig omega (WkN j) = return empty
    freeOmegaName sig omega (Ext sigma t) = M.do
      [| unite (freeOmegaName sig omega sigma) (freeOmegaName sig omega t) |]

  namespace SubstContext
    public export
    freeOmegaName : Signature -> Omega -> SubstContext -> M (Set OmegaName)
    freeOmegaName sig omega sigma = freeOmegaName sig omega (eval sigma)

  public export
  freeOmegaNameNu : Signature -> Omega -> Elem -> M (Set OmegaName)
  freeOmegaNameNu sig omega (PiTy x dom cod) = M.do
    [| unite (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) |]
  freeOmegaNameNu sig omega (ImplicitPiTy x dom cod) = M.do
    [| unite (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) |]
  freeOmegaNameNu sig omega (SigmaTy x dom cod) = M.do
    [| unite (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) |]
  freeOmegaNameNu sig omega (PiVal x dom cod f) = M.do
    [| unite3 (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) (freeOmegaName sig omega f) |]
  freeOmegaNameNu sig omega (ImplicitPiVal x dom cod f) =
    [| unite3 (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) (freeOmegaName sig omega f) |]
  freeOmegaNameNu sig omega (SigmaVal p q) =
    [| unite (freeOmegaName sig omega p) (freeOmegaName sig omega q) |]
  freeOmegaNameNu sig omega (PiElim f x dom cod e) = M.do
    [|
       unite4 (freeOmegaName sig omega f)
              (freeOmegaName sig omega dom)
              (freeOmegaName sig omega cod)
              (freeOmegaName sig omega e)
    |]
  freeOmegaNameNu sig omega (ImplicitPiElim f x dom cod e) = M.do
    [|
       unite4 (freeOmegaName sig omega f)
              (freeOmegaName sig omega dom)
              (freeOmegaName sig omega cod)
              (freeOmegaName sig omega e)
    |]
  freeOmegaNameNu sig omega (SigmaElim1 f x dom cod) = M.do
    [| unite3 (freeOmegaName sig omega f) (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) |]
  freeOmegaNameNu sig omega (SigmaElim2 f x dom cod) = M.do
    [| unite3 (freeOmegaName sig omega f) (freeOmegaName sig omega dom) (freeOmegaName sig omega cod) |]
  freeOmegaNameNu sig omega Universe = return empty
  freeOmegaNameNu sig omega NatVal0 = return empty
  freeOmegaNameNu sig omega (NatVal1 t) = freeOmegaName sig omega t
  freeOmegaNameNu sig omega NatTy = return empty
  freeOmegaNameNu sig omega (NatElim x schema z y h s t) = M.do
    [| unite4
         (freeOmegaName sig omega schema)
         (freeOmegaName sig omega z)
         (freeOmegaName sig omega s)
         (freeOmegaName sig omega t)
    |]
  freeOmegaNameNu sig omega (ContextSubstElim x y) = assert_total $ idris_crash "freeOmegaNameNu(ContextSubstElim)"
  freeOmegaNameNu sig omega (SignatureSubstElim x y) = assert_total $ idris_crash "freeOmegaNameNu(SignatureSubstElim)"
  freeOmegaNameNu sig omega (ContextVarElim j) = return empty
  freeOmegaNameNu sig omega (SignatureVarElim j sigma) = freeOmegaName sig omega sigma
  freeOmegaNameNu sig omega (OmegaVarElim j sigma) = M.do
    sigma <- freeOmegaName sig omega sigma
    return (insert j sigma)
  freeOmegaNameNu sig omega (EqTy a b ty) = M.do
    [| unite3 (freeOmegaName sig omega a) (freeOmegaName sig omega b) (freeOmegaName sig omega ty) |]
  freeOmegaNameNu sig omega EqVal = return empty

  ||| Compute free occurrences of Ω variables in the term modulo open evaluation.
  public export
  freeOmegaName : Signature -> Omega -> Elem -> M (Set OmegaName)
  freeOmegaName sig omega t = freeOmegaNameNu sig omega !(openEval sig omega t)

namespace Context
  public export
  freeOmegaName : Signature -> Omega -> Context -> M (Set OmegaName)
  freeOmegaName sig omega [<] = return empty
  freeOmegaName sig omega (ctx :< (x, ty)) = M.do
    [| unite (freeOmegaName sig omega ctx) (freeOmegaName sig omega ty) |]

