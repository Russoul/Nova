module Nova.Surface.Tactic.Unfold

import Data.Fin
import Data.Location
import Data.SnocList
import Data.Util

import Nova.Core.Context
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Evaluation
import Nova.Core.Conversion

import Nova.Surface.Language

-- This module contains support code for the unfold tactic
-- This tactic unfolds the head symbol once and computes normal form of the result

mutual
  namespace Typ
    ||| Try applying reduce tactic on a well-typed term
    ||| Γ ⊦ t : T
    ||| or
    ||| Γ ⊦ T type
    ||| The term must be head-neutral w.r.t. open evaluation
    ||| OpFreeTerm must represent a valid path!
    ||| See Surface/Language for a description of being a valid path.
    public export
    applyUnfoldNu : Signature -> Omega -> SnocList VarName -> Typ -> OpFreeTerm -> M (Either Range Typ)
    applyUnfoldNu sig omega ctx el (App _ (Tm _ tm) []) = MEither.do
      applyUnfold sig omega ctx el tm
    applyUnfoldNu sig omega ctx el (App _ (Underscore _) []) = MEither.do
      return el
    applyUnfoldNu sig omega ctx (El el) path = MEither.do
      return $ El !(applyUnfold sig omega ctx el path)
    applyUnfoldNu sig omega ctx (PiTy x dom cod) (PiTy r _ pdom pcod) = MEither.do
      return $ PiTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (PiTy x dom cod) (FunTy r pdom pcod) = MEither.do
      return $ PiTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (PiTy x dom cod) p = error (range p)
    applyUnfoldNu sig omega ctx (ImplicitPiTy x dom cod) (ImplicitPiTy r _ pdom pcod) = MEither.do
      return $ ImplicitPiTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (ImplicitPiTy x dom cod) p = error (range p)
    applyUnfoldNu sig omega ctx (SigmaTy x dom cod) (SigmaTy r _ pdom pcod) = MEither.do
      return $ SigmaTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (SigmaTy x dom cod) p = error (range p)
    applyUnfoldNu sig omega ctx UniverseTy p = error (range p)
    applyUnfoldNu sig omega ctx NatTy p = error (range p)
    applyUnfoldNu sig omega ctx ZeroTy p = error (range p)
    applyUnfoldNu sig omega ctx OneTy p = error (range p)
    applyUnfoldNu sig omega ctx (ContextSubstElim x y) f = assert_total $ idris_crash "applyUnfoldNu(_[_])"
    applyUnfoldNu sig omega ctx (SignatureSubstElim x y) f = assert_total $ idris_crash "applyUnfoldNu(_[_])"
    applyUnfoldNu sig omega ctx (OmegaVarElim str x) p = error (range p)
    applyUnfoldNu sig omega ctx (TyEqTy a b) (TyEqTy _ pa pb) = MEither.do
      return (TyEqTy !(applyUnfold sig omega ctx a pa) !(applyUnfold sig omega ctx b pb))
    applyUnfoldNu sig omega ctx (TyEqTy a b) p = error (range p)
    applyUnfoldNu sig omega ctx (ElEqTy a b ty) (ElEqTy _ pa pb pty) = MEither.do
      return (ElEqTy !(applyUnfold sig omega ctx a pa) !(applyUnfold sig omega ctx b pb) !(applyUnfold sig omega ctx ty pty))
    applyUnfoldNu sig omega ctx (ElEqTy a b ty) p = error (range p)

    public export
    applyUnfold : Signature -> Omega -> SnocList VarName -> Typ -> OpFreeTerm -> M (Either Range Typ)
    applyUnfold sig omega ctx t p = MEither.do
      applyUnfoldNu sig omega ctx !(liftM $ openEval sig omega t) p

  namespace Elem
    ||| Try applying reduce tactic on a well-typed term
    ||| Γ ⊦ t : T
    ||| or
    ||| Γ ⊦ T type
    ||| The term must be head-neutral w.r.t. open evaluation
    ||| OpFreeTerm must represent a valid path!
    ||| See Surface/Language for a description of being a valid path.
    public export
    applyUnfoldNu : Signature -> Omega -> SnocList VarName -> Elem -> OpFreeTerm -> M (Either Range Elem)
    applyUnfoldNu sig omega ctx el (App _ (Tm _ tm) []) = MEither.do
      applyUnfold sig omega ctx el tm
    applyUnfoldNu sig omega ctx here (App r (Box _) []) = MEither.do
      here <- applyUnfoldNuHelper sig omega here r
      liftM $ openEval sig omega here
    applyUnfoldNu sig omega ctx here (App r (Underscore _) []) = MEither.do
      return here
    applyUnfoldNu sig omega ctx (PiTy x dom cod) (PiTy r _ pdom pcod) = MEither.do
      return $ PiTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (PiTy x dom cod) (FunTy r pdom pcod) = MEither.do
      return $ PiTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (PiTy x dom cod) p = error (range p)
    applyUnfoldNu sig omega ctx (ImplicitPiTy x dom cod) (ImplicitPiTy r _ pdom pcod) = MEither.do
      return $ ImplicitPiTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (ImplicitPiTy x dom cod) p = error (range p)
    applyUnfoldNu sig omega ctx (SigmaTy x dom cod) (SigmaTy r _ pdom pcod) = MEither.do
      return $ SigmaTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (SigmaTy x dom cod) (ProdTy r pdom pcod) = MEither.do
      return $ SigmaTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (SigmaTy x dom cod) p = error (range p)
    applyUnfoldNu sig omega ctx (PiVal x a b body) (PiVal r _ pbody) = MEither.do
      return $ PiVal x a b !(applyUnfold sig omega (ctx :< x) body pbody)
    applyUnfoldNu sig omega ctx (PiVal x a b body) p = error (range p)
    applyUnfoldNu sig omega ctx (ImplicitPiVal x a b body) (ImplicitPiVal r _ pbody) = MEither.do
      return $ ImplicitPiVal x a b !(applyUnfold sig omega (ctx :< x) body pbody)
    applyUnfoldNu sig omega ctx (ImplicitPiVal x a b body) p = error (range p)
    applyUnfoldNu sig omega ctx (SigmaVal a b) (SigmaVal r pa pb) = MEither.do
      return $ SigmaVal !(applyUnfold sig omega ctx a pa) !(applyUnfold sig omega ctx b pb)
    applyUnfoldNu sig omega ctx (SigmaVal a b) p = error (range p)
    applyUnfoldNu sig omega ctx (PiElim f x a b e) (App r h es) = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error r
        (es :< (_, Arg ([], pe))) => MEither.do
          return $ PiElim !(applyUnfold sig omega ctx f (App r h (cast es))) x a b !(applyUnfold sig omega ctx e pe)
        (es :< (r, _)) => MEither.do
          error r
    applyUnfoldNu sig omega ctx (PiElim f x a b e) p = error (range p)
    applyUnfoldNu sig omega ctx (ImplicitPiElim f x a b e) (App r h es) = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        (es :< (_, ImplicitArg pe)) => MEither.do
          return $ ImplicitPiElim !(applyUnfold sig omega ctx f (App r h (cast es))) x a b !(applyUnfold sig omega ctx e pe)
        es => MEither.do
          return $ ImplicitPiElim !(applyUnfold sig omega ctx f (App r h (cast es))) x a b e
    applyUnfoldNu sig omega ctx (ImplicitPiElim f x a b e) p = MEither.do
      return $ ImplicitPiElim !(applyUnfold sig omega ctx f p) x a b e
    applyUnfoldNu sig omega ctx (SigmaElim1 f x a b) (App r h es) = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error r
        (es :< (_, Pi1)) => MEither.do
          return $ SigmaElim1 !(applyUnfold sig omega ctx f (App r h (cast es))) x a b
        (es :< (r, _)) => MEither.do
          error r
    applyUnfoldNu sig omega ctx (SigmaElim1 f x a b) p = error (range p)
    applyUnfoldNu sig omega ctx (SigmaElim2 f x a b) (App r h es) = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error r
        (es :< (_, Pi2)) => MEither.do
          return $ SigmaElim2 !(applyUnfold sig omega ctx f (App r h (cast es))) x a b
        (es :< (r, _)) => MEither.do
          error r
    applyUnfoldNu sig omega ctx (SigmaElim2 f x a b) p = error (range p)
    applyUnfoldNu sig omega ctx NatVal0 p = error (range p)
    applyUnfoldNu sig omega ctx (NatVal1 t) (App r (NatVal1 _) [(_, Arg ([], p))]) = MEither.do
      return $ NatVal1 !(applyUnfold sig omega ctx t p)
    applyUnfoldNu sig omega ctx (NatVal1 t) p = error (range p)
    applyUnfoldNu sig omega ctx OneVal p = error (range p)
    applyUnfoldNu sig omega ctx NatTy p = error (range p)
    applyUnfoldNu sig omega ctx ZeroTy p = error (range p)
    applyUnfoldNu sig omega ctx OneTy p = error (range p)
    applyUnfoldNu sig omega ctx (ZeroElim t) p = error (range p)
    applyUnfoldNu sig omega ctx (NatElim x schema z y h s t) (App r (NatElim _)
                                                              [(_, Arg ([], pschema)),
                                                               (_, Arg ([], pz)),
                                                               (_, Arg ([], ps)),
                                                               (_, Arg ([], pt))]
                                                         ) = MEither.do
      return (NatElim x !(applyUnfold sig omega (ctx :< x) schema pschema)
                        !(applyUnfold sig omega ctx z pz)
                        y
                        h
                        !(applyUnfold sig omega (ctx :< y :< h) s ps)
                        !(applyUnfold sig omega ctx t pt)
             )
    applyUnfoldNu sig omega ctx (NatElim x schema z y h s t) p = error (range p)
    applyUnfoldNu sig omega ctx (ContextSubstElim x y) f = assert_total $ idris_crash "applyUnfoldNu(_[_])"
    applyUnfoldNu sig omega ctx (SignatureSubstElim x y) f = assert_total $ idris_crash "applyUnfoldNu(_[_])"
    applyUnfoldNu sig omega ctx (ContextVarElim k) (App r (Var _ y) []) = MEither.do
      case mbIndex k ctx of
        Just (_, x, _) =>
          case x == y of
            True => return (ContextVarElim k)
            False => error r
        Nothing => error r
    applyUnfoldNu sig omega ctx (ContextVarElim k) p = error (range p)
    applyUnfoldNu sig omega ctx (OmegaVarElim str x) p = error (range p)
    applyUnfoldNu sig omega ctx (TyEqTy a b) (TyEqTy _ pa pb) = MEither.do
      return (TyEqTy !(applyUnfold sig omega ctx a pa) !(applyUnfold sig omega ctx b pb))
    applyUnfoldNu sig omega ctx (TyEqTy a b) p = error (range p)
    applyUnfoldNu sig omega ctx (ElEqTy a b ty) (ElEqTy _ pa pb pty) = MEither.do
      return (ElEqTy !(applyUnfold sig omega ctx a pa) !(applyUnfold sig omega ctx b pb) !(applyUnfold sig omega ctx ty pty))
    applyUnfoldNu sig omega ctx (ElEqTy a b ty) p = error (range p)
    applyUnfoldNu sig omega ctx TyEqVal p = error (range p)
    applyUnfoldNu sig omega ctx ElEqVal p = error (range p)
    applyUnfoldNu sig omega ctx tm@(SignatureVarElim x subst) (App r (Var _ y) []) = MEither.do
      case !(liftM $ conv sig omega subst Terminal) of
        True =>
          case lookupSignature sig x of
            Just (x, _) =>
              case x == y of
                True => return tm
                False => error r
            Nothing => throw "applyUnfoldNu(SignatureVarElim)"
        False => error r
    applyUnfoldNu sig omega ctx (SignatureVarElim x sigma) p = throw "applyUnfold(1): \{show p}"

    public export
    applyUnfoldNuHelper : Signature -> Omega -> Elem -> Range -> M (Either Range Elem)
    applyUnfoldNuHelper sig omega (PiTy str x y) r = error r
    applyUnfoldNuHelper sig omega (ImplicitPiTy str x y) r = error r
    applyUnfoldNuHelper sig omega (SigmaTy str x y) r = error r
    applyUnfoldNuHelper sig omega (PiVal str x y z) r = error r
    applyUnfoldNuHelper sig omega (ImplicitPiVal str x y z) r = error r
    applyUnfoldNuHelper sig omega (SigmaVal x y) r = error r
    applyUnfoldNuHelper sig omega (PiElim f x dom cod e) r = MEither.do
      f <- applyUnfoldNuHelper sig omega f r
      return (PiElim f x dom cod e)
    applyUnfoldNuHelper sig omega (ImplicitPiElim f x dom cod e) r = MEither.do
      f <- applyUnfoldNuHelper sig omega f r
      return (ImplicitPiElim f x dom cod e)
    applyUnfoldNuHelper sig omega (SigmaElim1 f x dom cod) r = MEither.do
      f <- applyUnfoldNuHelper sig omega f r
      return (SigmaElim1 f x dom cod)
    applyUnfoldNuHelper sig omega (SigmaElim2 f x dom cod) r = MEither.do
      f <- applyUnfoldNuHelper sig omega f r
      return (SigmaElim2 f x dom cod)
    applyUnfoldNuHelper sig omega NatVal0 r = error r
    applyUnfoldNuHelper sig omega (NatVal1 x) r = error r
    applyUnfoldNuHelper sig omega NatTy r = error r
    applyUnfoldNuHelper sig omega (NatElim x schema z y h s t) r = MEither.do
      t <- applyUnfoldNuHelper sig omega t r
      return (NatElim x schema z y h s t)
    applyUnfoldNuHelper sig omega (ContextSubstElim x y) r = assert_total $ idris_crash "applyUnfoldNuHelper(ContextSubstElim)"
    applyUnfoldNuHelper sig omega (SignatureSubstElim x y) r = assert_total $ idris_crash "applyUnfoldNuHelper(SignatureSubstElim)"
    applyUnfoldNuHelper sig omega (ContextVarElim k) r = error r
    applyUnfoldNuHelper sig omega (SignatureVarElim x sigma) r = M.do
      case lookupSignature sig x of
        Just (x, LetElemEntry ctx rhs ty) =>
          return (ContextSubstElim rhs sigma)
        Just (x, _) => error r
        Nothing => throw "applyUnfoldNu(SignatureVarElim)"
    applyUnfoldNuHelper sig omega (OmegaVarElim str x) r = error r
    applyUnfoldNuHelper sig omega (TyEqTy x y) r = error r
    applyUnfoldNuHelper sig omega (ElEqTy x y z) r = error r
    applyUnfoldNuHelper sig omega TyEqVal r = error r
    applyUnfoldNuHelper sig omega ElEqVal r = error r
    applyUnfoldNuHelper sig omega ZeroTy r = error r
    applyUnfoldNuHelper sig omega OneTy r = error r
    applyUnfoldNuHelper sig omega OneVal r = error r
    applyUnfoldNuHelper sig omega (ZeroElim x) r = error r

    public export
    applyUnfold : Signature -> Omega -> SnocList VarName -> Elem -> OpFreeTerm -> M (Either Range Elem)
    applyUnfold sig omega ctx t p = MEither.do
      applyUnfoldNu sig omega ctx !(liftM $ openEval sig omega t) p
