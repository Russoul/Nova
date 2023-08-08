module ETT.Core.Evaluation

import Data.Util

import ETT.Core.Monad
import ETT.Core.Language
import ETT.Core.Substitution

-- Closed term evaluation

lookupContextInst : ContextInst -> Nat -> M Elem
lookupContextInst [<] _ = throw "Exception in lookupContextInst"
lookupContextInst (ts :< t) 0 = return t
lookupContextInst (ts :< t) (S k) = lookupContextInst ts k

lookupSignatureInst : SignatureInst -> Nat -> M Elem
lookupSignatureInst [<] _ = throw "Exception in lookupSignatureInst"
lookupSignatureInst (ts :< t) 0 = return t
lookupSignatureInst (ts :< t) (S k) = lookupSignatureInst ts k

||| Γ₀ (xᵢ : A) Γ₁ ⊦ xᵢ : A
lookupLetElemSignature : Signature -> Nat -> M Elem
lookupLetElemSignature [<] x = throw "lookupLetElemSignature(1)"
lookupLetElemSignature (sig :< (_, LetElemEntry ctx e ty _)) 0 = return $ SignatureSubstElim e Wk
lookupLetElemSignature (sig :< (_, _)) 0 = throw "lookupLetElemSignature(2)"
lookupLetElemSignature (sig :< (_, _)) (S k) = M.do
  t <- lookupLetElemSignature sig k
  return (SignatureSubstElim t Wk)

mutual
  ||| Σ ⊦ a ⇝ a' : A
  ||| Σ must only contain let-elem's
  public export
  closedEvalNu : Signature -> Elem -> M Elem
  closedEvalNu sig NatTy = return NatTy
  closedEvalNu sig Universe = return Universe
  closedEvalNu sig (PiTy x a b) = return (PiTy x a b)
  closedEvalNu sig (PiVal x a b f) = return (PiVal x a b f)
  closedEvalNu sig (PiElim f x a b e) = M.do
    PiVal _ _ _ f <- closedEval sig f
      | _ => throw "closedEval(PiElim)"
    closedEval sig (ContextSubstElim f (Ext Terminal e))
  closedEvalNu sig NatVal0 = return NatVal0
  closedEvalNu sig (NatVal1 t) = return (NatVal1 t)
  closedEvalNu sig (NatElim x schema z y h s t) = M.do
    t <- closedEval sig t
    case t of
      NatVal0 => closedEval sig z
      NatVal1 t => closedEval sig (ContextSubstElim s (Ext (Ext Terminal t) (NatElim x schema z y h s t)))
      _ => throw "closedEval(NatElim)"
  closedEvalNu sig (ContextSubstElim t sigma) = throw "closedEval(ContextSubstElim)"
  closedEvalNu sig (SignatureSubstElim t sigma) = throw "closedEval(SignatureSubstElim)"
  closedEvalNu sig (ContextVarElim x) = throw "closedEval(ContextVarElim)"
  -- Σ₀ (Γ ⊦ x ≔ e : A) Σ₁ ⊦ x σ = e(↑(1 + |Σ₁|))(σ)
  closedEvalNu sig (SignatureVarElim x spine) = M.do
   t <- lookupLetElemSignature sig x
   closedEval sig (ContextSubstElim t spine)
  closedEvalNu sig (EqTy a0 a1 ty) = return $ EqTy a0 a1 ty
  closedEvalNu sig EqVal = return EqVal

  ||| Σ ⊦ a ⇝ a' : A
  ||| Σ must only contain let-elem's
  public export
  closedEval : Signature -> Elem -> M Elem
  closedEval sig tm = closedEvalNu sig (runSubst tm)

mutual
  ||| Σ ⊦ a ⇝ a' : A
  ||| Σ must only contain let-elem's
  public export
  openEvalNu : Signature -> Elem -> M Elem
  openEvalNu sig NatTy = return NatTy
  openEvalNu sig Universe = return Universe
  openEvalNu sig (PiTy x a b) = return (PiTy x a b)
  openEvalNu sig (PiVal x a b f) = return (PiVal x a b f)
  openEvalNu sig (PiElim f x a b e) = M.do
    return (PiElim f x a b e)
  openEvalNu sig NatVal0 = return NatVal0
  openEvalNu sig (NatVal1 t) = return (NatVal1 t)
  openEvalNu sig (NatElim x schema z y h s t) = M.do
    return (NatElim x schema z y h s t)
  openEvalNu sig (ContextSubstElim t sigma) = throw "openEval(ContextSubstElim)"
  openEvalNu sig (SignatureSubstElim t sigma) = throw "openEval(SignatureSubstElim)"
  openEvalNu sig (ContextVarElim x) = return (ContextVarElim x)
  -- Σ₀ (Γ ⊦ x ≔ e : A) Σ₁ ⊦ x σ = e(↑(1 + |Σ₁|))(σ)
  openEvalNu sig (SignatureVarElim k sigma) = M.do
    let Just (_, (_, entry), rest) = splitAt sig k
      | Nothing => throw "openEvalNu(SigmaVarElim)"
    case (subst entry (WkN (1 + length rest))) of
      LetElemEntry _ rhs _ True => openEval sig (ContextSubstElim rhs sigma)
      _ => return (SignatureVarElim k sigma)
  openEvalNu sig (EqTy a0 a1 ty) = return $ EqTy a0 a1 ty
  openEvalNu sig EqVal = return EqVal

  ||| Σ ⊦ a ⇝ a' : A
  ||| Computes head-normal form w.r.t. (~) relation used in unification.
  public export
  openEval : Signature -> Elem -> M Elem
  openEval sig tm = openEvalNu sig (runSubst tm)
