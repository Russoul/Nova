module ETT.Core.Evaluation

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
lookupLetElemSignature (sig :< (_, LetElemEntry ctx e ty)) 0 = return $ SignatureSubstElim e Wk
lookupLetElemSignature (sig :< (_, _)) 0 = throw "lookupLetElemSignature(2)"
lookupLetElemSignature (sig :< (_, _)) (S k) = M.do
  t <- lookupLetElemSignature sig k
  return (SignatureSubstElim t Wk)

mutual
  ||| Σ ⊦ a ⇝ a' : A
  ||| Σ must only contain let-elem's
  public export
  evalNu : Signature -> Elem -> M Elem
  evalNu sig NatTy = return NatTy
  evalNu sig Universe = return Universe
  evalNu sig (PiTy x a b) = return (PiTy x a b)
  evalNu sig (PiVal x a b f) = return (PiVal x a b f)
  evalNu sig (PiElim f x a b e) = M.do
    PiVal _ _ _ f <- eval sig f
      | _ => throw "eval(PiElim)"
    eval sig (ContextSubstElim f (Ext Terminal e))
  evalNu sig NatVal0 = return NatVal0
  evalNu sig (NatVal1 t) = return (NatVal1 t)
  evalNu sig (NatElim x schema z y h s t) = M.do
    t <- eval sig t
    case t of
      NatVal0 => eval sig z
      NatVal1 t => eval sig (ContextSubstElim s (Ext (Ext Terminal t) (NatElim x schema z y h s t)))
      _ => throw "eval(NatElim)"
  evalNu sig (ContextSubstElim t sigma) = throw "eval(ContextSubstElim)"
  evalNu sig (SignatureSubstElim t sigma) = throw "eval(SignatureSubstElim)"
  evalNu sig (ContextVarElim x) = throw "eval(ContextVarElim)"
  -- Σ₀ (Γ ⊦ x ≔ e : A) Σ₁ ⊦ x σ = e(↑(1 + |Σ₁|))(σ)
  evalNu sig (SignatureVarElim x spine) = M.do
   t <- lookupLetElemSignature sig x
   eval sig (ContextSubstElim t spine)
  evalNu sig (EqTy a0 a1 ty) = return $ EqTy a0 a1 ty
  evalNu sig EqVal = return EqVal
  evalNu sig (EqElim ty a0 x p schema r a1 a) = eval sig r

  ||| Σ ⊦ a ⇝ a' : A
  ||| Σ must only contain let-elem's
  public export
  eval : Signature -> Elem -> M Elem
  eval sig tm = evalNu sig (runSubst tm)
