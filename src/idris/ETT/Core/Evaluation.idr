module ETT.Core.Evaluation

import Control.Monad.FailSt

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

mutual
  ||| a ⇝ a' : A
  public export
  evalNu : Elem -> M Elem
  evalNu NatTy = return NatTy
  evalNu (PiTy x a b) = return (PiTy x a b)
  evalNu (PiVal x a b f) = return (PiVal x a b f)
  evalNu (PiElim f x a b e) = FailSt.do
    PiVal _ _ _ f <- eval f
      | _ => throw "eval(PiElim)"
    eval (ContextSubstElim f (Ext Terminal e))
  evalNu NatVal0 = return NatVal0
  evalNu (NatVal1 t) = return (NatVal1 t)
  evalNu (NatElim x schema z y h s t) = FailSt.do
    t <- eval t
    case t of
      NatVal0 => eval z
      NatVal1 t => eval (ContextSubstElim s (Ext (Ext Terminal t) (NatElim x schema z y h s t)))
      _ => throw "eval(NatElim)"
  evalNu (ContextSubstElim t sigma) = throw "eval(ContextSubstElim)"
  evalNu (SignatureSubstElim t sigma) = throw "eval(SignatureSubstElim)"
  evalNu (ContextVarElim x) = throw "eval(ContextVarElim)"
  evalNu (SignatureVarElim x spine) = throw "eval(SignatureVarElim)"
  evalNu (EqTy a0 a1 ty) = return $ EqTy a0 a1 ty
  evalNu EqVal = return EqVal
  evalNu (EqElim ty a0 x p schema r a1 a) = eval r

  ||| a ⇝ a' : A
  public export
  eval : Elem -> M Elem
  eval tm = evalNu (runSubst tm)
