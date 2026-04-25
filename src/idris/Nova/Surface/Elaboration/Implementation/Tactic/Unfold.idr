module Nova.Surface.Elaboration.Implementation.Tactic.Unfold

import Me.Russoul.Data.Location

import Nova.Control.Monad.Id

import Data.Fin
import Data.SnocList
import Data.Util

import Nova.Core.Context
import Nova.Core.Language
import Nova.Core.Evaluation
import Nova.Core.Conversion

import Nova.Surface.Language

-- This module contains support code for the unfold tactic
-- This tactic unfolds the head symbol once and computes normal form of the result

mutual
  namespace Ctx
    ||| Try applying reduce tactic on a well-typed ctx
    ||| Γ ctx
    ||| The term must be head-neutral w.r.t. open evaluation
    ||| OpFreeCtxPath must represent a valid path!
    ||| See Surface/Language for a description of being a valid path.
    public export
    applyUnfold : Signature -> Omega -> Context -> OpFreeCtxPath -> Either Range Context
    applyUnfold sig omega (ctx :< (x, typ)) (MkOpFreeCtxPath r here 0) = Prelude.do
      typ <- applyUnfold sig omega (map fst ctx) typ here
      Right (ctx :< (x, typ))
    applyUnfold sig omega (ctx :< (x, typ)) (MkOpFreeCtxPath r here (S n)) = with Prelude.(<&>)
      applyUnfold sig omega ctx (MkOpFreeCtxPath r here n) <&> (:< (x, typ))
    applyUnfold sig omega [<] (MkOpFreeCtxPath r here _) = Left r

  namespace Typ
    ||| Try applying reduce tactic on a well-typed term
    ||| Γ ⊦ t : T
    ||| or
    ||| Γ ⊦ T type
    ||| The term must be head-neutral w.r.t. open evaluation
    ||| OpFreeTerm must represent a valid path!
    ||| See Surface/Language for a description of being a valid path.
    public export
    applyUnfoldNu : Signature -> Omega -> SnocList VarName -> Typ -> OpFreeTerm -> Either Range Typ
    applyUnfoldNu sig omega ctx el (App _ (Tm _ tm) []) = Prelude.do
      applyUnfold sig omega ctx el tm
    applyUnfoldNu sig omega ctx el (App _ (Underscore _) []) = Prelude.do
      pure el
    applyUnfoldNu sig omega ctx (El el) path = Prelude.do
      pure $ El !(applyUnfold sig omega ctx el path)
    applyUnfoldNu sig omega ctx (PiTy x dom cod) (PiTy r _ pdom pcod) = Prelude.do
      pure $ PiTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (PiTy x dom cod) (FunTy r pdom pcod) = Prelude.do
      pure $ PiTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (PiTy x dom cod) p = Left (range p)
    applyUnfoldNu sig omega ctx (ImplicitPiTy x dom cod) (ImplicitPiTy r _ pdom pcod) = Prelude.do
      pure $ ImplicitPiTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (ImplicitPiTy x dom cod) p = Left (range p)
    applyUnfoldNu sig omega ctx (SigmaTy x dom cod) (SigmaTy r _ pdom pcod) = Prelude.do
      pure $ SigmaTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (SigmaTy x dom cod) p = Left (range p)
    applyUnfoldNu sig omega ctx UniverseTy p = Left (range p)
    applyUnfoldNu sig omega ctx NatTy p = Left (range p)
    applyUnfoldNu sig omega ctx ZeroTy p = Left (range p)
    applyUnfoldNu sig omega ctx OneTy p = Left (range p)
    applyUnfoldNu sig omega ctx (ContextSubstElim x y) f = assert_total $ idris_crash "applyUnfoldNu(_[_])"
    applyUnfoldNu sig omega ctx (SignatureSubstElim x y) f = assert_total $ idris_crash "applyUnfoldNu(_[_])"
    applyUnfoldNu sig omega ctx (OmegaVarElim str x) p = Left (range p)
    applyUnfoldNu sig omega ctx (TyEqTy a b) (TyEqTy _ pa pb) = Prelude.do
      pure (TyEqTy !(applyUnfold sig omega ctx a pa) !(applyUnfold sig omega ctx b pb))
    applyUnfoldNu sig omega ctx (TyEqTy a b) p = Left (range p)
    applyUnfoldNu sig omega ctx (ElEqTy a b ty) (ElEqTy _ pa pb pty) = Prelude.do
      pure (ElEqTy !(applyUnfold sig omega ctx a pa) !(applyUnfold sig omega ctx b pb) !(applyUnfold sig omega ctx ty pty))
    applyUnfoldNu sig omega ctx (ElEqTy a b ty) p = Left (range p)
    applyUnfoldNu sig omega ctx tm@(SignatureVarElim x subst) (App r (Var _ y) []) = Prelude.do
      case conv sig omega subst Terminal of
        True =>
          case lookupSignature sig x of
            Just (x, _) =>
              case x == y of
                True => pure tm
                False => Left r
            Nothing => assert_total $ idris_crash "applyUnfoldNu(SignatureVarElim)"
        False => Left r
    applyUnfoldNu sig omega ctx tm@(SignatureVarElim x sigma) (App r (Box _) []) = Prelude.do
      case lookupSignature sig x of
        Just (x, LetTypeEntry ctx rhs) =>
          pure (ContextSubstElim rhs sigma)
        Just (x, _) => Left r
        Nothing => assert_total $ idris_crash "applyUnfoldNu(SignatureVarElim)"
    applyUnfoldNu sig omega ctx (SignatureVarElim x sigma) p = Left (range p)

    public export
    applyUnfold : Signature -> Omega -> SnocList VarName -> Typ -> OpFreeTerm -> Either Range Typ
    applyUnfold sig omega ctx t p = Prelude.do
      applyUnfoldNu sig omega ctx (openEval sig omega t) p

  namespace Elem
    ||| Try applying reduce tactic on a well-typed term
    ||| Γ ⊦ t : T
    ||| or
    ||| Γ ⊦ T type
    ||| The term must be head-neutral w.r.t. open evaluation
    ||| OpFreeTerm must represent a valid path!
    ||| See Surface/Language for a description of being a valid path.
    public export
    applyUnfoldNu : Signature -> Omega -> SnocList VarName -> Elem -> OpFreeTerm -> Either Range Elem
    applyUnfoldNu sig omega ctx el (App _ (Tm _ tm) []) = Prelude.do
      applyUnfold sig omega ctx el tm
    applyUnfoldNu sig omega ctx here (App r (Box _) []) = Prelude.do
      here <- applyUnfoldNuHelper sig omega here r
      Right $ openEval sig omega here
    applyUnfoldNu sig omega ctx here (App r (Underscore _) []) = Prelude.do
      pure here
    applyUnfoldNu sig omega ctx (PiTy x dom cod) (PiTy r _ pdom pcod) = Prelude.do
      pure $ PiTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (PiTy x dom cod) (FunTy r pdom pcod) = Prelude.do
      pure $ PiTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (PiTy x dom cod) p = Left (range p)
    applyUnfoldNu sig omega ctx (ImplicitPiTy x dom cod) (ImplicitPiTy r _ pdom pcod) = Prelude.do
      pure $ ImplicitPiTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (ImplicitPiTy x dom cod) p = Left (range p)
    applyUnfoldNu sig omega ctx (SigmaTy x dom cod) (SigmaTy r _ pdom pcod) = Prelude.do
      pure $ SigmaTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (SigmaTy x dom cod) (ProdTy r pdom pcod) = Prelude.do
      pure $ SigmaTy x !(applyUnfold sig omega ctx dom pdom) !(applyUnfold sig omega (ctx :< x) cod pcod)
    applyUnfoldNu sig omega ctx (SigmaTy x dom cod) p = Left (range p)
    applyUnfoldNu sig omega ctx (PiVal x a b body) (PiVal r _ pbody) = Prelude.do
      pure $ PiVal x a b !(applyUnfold sig omega (ctx :< x) body pbody)
    applyUnfoldNu sig omega ctx (PiVal x a b body) p = Left (range p)
    applyUnfoldNu sig omega ctx (ImplicitPiVal x a b body) (ImplicitPiVal r _ pbody) = Prelude.do
      pure $ ImplicitPiVal x a b !(applyUnfold sig omega (ctx :< x) body pbody)
    applyUnfoldNu sig omega ctx (ImplicitPiVal x a b body) p = Left (range p)
    applyUnfoldNu sig omega ctx (SigmaVal x dom cod a b) (SigmaVal r pa pb) = Prelude.do
      pure $ SigmaVal x dom cod !(applyUnfold sig omega ctx a pa) !(applyUnfold sig omega ctx b pb)
    applyUnfoldNu sig omega ctx (SigmaVal x dom cod a b) p = Left (range p)
    applyUnfoldNu sig omega ctx (PiElim f x a b e) (App r h es) = Prelude.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => Left r
        (es :< (_, Arg ([], pe))) => Prelude.do
          pure $ PiElim !(applyUnfold sig omega ctx f (App r h (cast es))) x a b !(applyUnfold sig omega ctx e pe)
        (es :< (r, _)) => Prelude.do
          Left r
    applyUnfoldNu sig omega ctx (PiElim f x a b e) p = Left (range p)
    applyUnfoldNu sig omega ctx (ImplicitPiElim f x a b e) (App r h es) = Prelude.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        (es :< (_, ImplicitArg pe)) => Prelude.do
          pure $ ImplicitPiElim !(applyUnfold sig omega ctx f (App r h (cast es))) x a b !(applyUnfold sig omega ctx e pe)
        es => Prelude.do
          pure $ ImplicitPiElim !(applyUnfold sig omega ctx f (App r h (cast es))) x a b e
    applyUnfoldNu sig omega ctx (ImplicitPiElim f x a b e) p = Prelude.do
      pure $ ImplicitPiElim !(applyUnfold sig omega ctx f p) x a b e
    applyUnfoldNu sig omega ctx (SigmaElim1 f x a b) (App r h es) = Prelude.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => Left r
        (es :< (_, Pi1)) => Prelude.do
          pure $ SigmaElim1 !(applyUnfold sig omega ctx f (App r h (cast es))) x a b
        (es :< (r, _)) => Prelude.do
          Left r
    applyUnfoldNu sig omega ctx (SigmaElim1 f x a b) p = Left (range p)
    applyUnfoldNu sig omega ctx (SigmaElim2 f x a b) (App r h es) = Prelude.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => Left r
        (es :< (_, Pi2)) => Prelude.do
          pure $ SigmaElim2 !(applyUnfold sig omega ctx f (App r h (cast es))) x a b
        (es :< (r, _)) => Prelude.do
          Left r
    applyUnfoldNu sig omega ctx (SigmaElim2 f x a b) p = Left (range p)
    applyUnfoldNu sig omega ctx NatVal0 p = Left (range p)
    applyUnfoldNu sig omega ctx (NatVal1 t) (App r (NatVal1 _) [(_, Arg ([], p))]) = Prelude.do
      pure $ NatVal1 !(applyUnfold sig omega ctx t p)
    applyUnfoldNu sig omega ctx (NatVal1 t) p = Left (range p)
    applyUnfoldNu sig omega ctx OneVal p = Left (range p)
    applyUnfoldNu sig omega ctx NatTy p = Left (range p)
    applyUnfoldNu sig omega ctx ZeroTy p = Left (range p)
    applyUnfoldNu sig omega ctx OneTy p = Left (range p)
    applyUnfoldNu sig omega ctx (ZeroElim ty t) p = Left (range p)
    applyUnfoldNu sig omega ctx (NatElim x schema z y h s t) (App r (NatElim _)
                                                              [(_, Arg ([], pschema)),
                                                               (_, Arg ([], pz)),
                                                               (_, Arg ([], ps)),
                                                               (_, Arg ([], pt))]
                                                         ) = Prelude.do
      pure (NatElim x !(applyUnfold sig omega (ctx :< x) schema pschema)
                        !(applyUnfold sig omega ctx z pz)
                        y
                        h
                        !(applyUnfold sig omega (ctx :< y :< h) s ps)
                        !(applyUnfold sig omega ctx t pt)
             )
    applyUnfoldNu sig omega ctx (NatElim x schema z y h s t) p = Left (range p)
    applyUnfoldNu sig omega ctx (ContextSubstElim x y) f = assert_total $ idris_crash "applyUnfoldNu(_[_])"
    applyUnfoldNu sig omega ctx (SignatureSubstElim x y) f = assert_total $ idris_crash "applyUnfoldNu(_[_])"
    applyUnfoldNu sig omega ctx (ContextVarElim k) (App r (Var _ y) []) = Prelude.do
      case mbIndex k ctx of
        Just (_, x, _) =>
          case x == y of
            True => pure (ContextVarElim k)
            False => Left r
        Nothing => Left r
    applyUnfoldNu sig omega ctx (ContextVarElim k) p = Left (range p)
    applyUnfoldNu sig omega ctx (OmegaVarElim str x) p = Left (range p)
    applyUnfoldNu sig omega ctx (TyEqTy a b) (TyEqTy _ pa pb) = Prelude.do
      pure (TyEqTy !(applyUnfold sig omega ctx a pa) !(applyUnfold sig omega ctx b pb))
    applyUnfoldNu sig omega ctx (TyEqTy a b) p = Left (range p)
    applyUnfoldNu sig omega ctx (ElEqTy a b ty) (ElEqTy _ pa pb pty) = Prelude.do
      pure (ElEqTy !(applyUnfold sig omega ctx a pa) !(applyUnfold sig omega ctx b pb) !(applyUnfold sig omega ctx ty pty))
    applyUnfoldNu sig omega ctx (ElEqTy a b ty) p = Left (range p)
    applyUnfoldNu sig omega ctx (TyEqVal ty) p = Left (range p)
    applyUnfoldNu sig omega ctx (ElEqVal ty e) p = Left (range p)
    applyUnfoldNu sig omega ctx tm@(SignatureVarElim x subst) (App r (Var _ y) []) = Prelude.do
      case conv sig omega subst Terminal of
        True =>
          case lookupSignature sig x of
            Just (x, _) =>
              case x == y of
                True => pure tm
                False => Left r
            Nothing => assert_total $ idris_crash "applyUnfoldNu(SignatureVarElim)"
        False => Left r
    applyUnfoldNu sig omega ctx (SignatureVarElim x sigma) p = assert_total $ idris_crash "applyUnfold(1): \{show p}"

    public export
    applyUnfoldNuHelper : Signature -> Omega -> Elem -> Range -> Either Range Elem
    applyUnfoldNuHelper sig omega (PiTy str x y) r = Left r
    applyUnfoldNuHelper sig omega (ImplicitPiTy str x y) r = Left r
    applyUnfoldNuHelper sig omega (SigmaTy str x y) r = Left r
    applyUnfoldNuHelper sig omega (PiVal str x y z) r = Left r
    applyUnfoldNuHelper sig omega (ImplicitPiVal str x y z) r = Left r
    applyUnfoldNuHelper sig omega (SigmaVal _ _ _ x y) r = Left r
    applyUnfoldNuHelper sig omega (PiElim f x dom cod e) r = Prelude.do
      f <- applyUnfoldNuHelper sig omega f r
      pure (PiElim f x dom cod e)
    applyUnfoldNuHelper sig omega (ImplicitPiElim f x dom cod e) r = Prelude.do
      f <- applyUnfoldNuHelper sig omega f r
      pure (ImplicitPiElim f x dom cod e)
    applyUnfoldNuHelper sig omega (SigmaElim1 f x dom cod) r = Prelude.do
      f <- applyUnfoldNuHelper sig omega f r
      pure (SigmaElim1 f x dom cod)
    applyUnfoldNuHelper sig omega (SigmaElim2 f x dom cod) r = Prelude.do
      f <- applyUnfoldNuHelper sig omega f r
      pure (SigmaElim2 f x dom cod)
    applyUnfoldNuHelper sig omega NatVal0 r = Left r
    applyUnfoldNuHelper sig omega (NatVal1 x) r = Left r
    applyUnfoldNuHelper sig omega NatTy r = Left r
    applyUnfoldNuHelper sig omega (NatElim x schema z y h s t) r = Prelude.do
      t <- applyUnfoldNuHelper sig omega t r
      pure (NatElim x schema z y h s t)
    applyUnfoldNuHelper sig omega (ContextSubstElim x y) r = assert_total $ idris_crash "applyUnfoldNuHelper(ContextSubstElim)"
    applyUnfoldNuHelper sig omega (SignatureSubstElim x y) r = assert_total $ idris_crash "applyUnfoldNuHelper(SignatureSubstElim)"
    applyUnfoldNuHelper sig omega (ContextVarElim k) r = Left r
    applyUnfoldNuHelper sig omega (SignatureVarElim x sigma) r = M.do
      case lookupSignature sig x of
        Just (x, LetElemEntry ctx rhs ty) =>
          pure (ContextSubstElim rhs sigma)
        Just (x, _) => Left r
        Nothing => assert_total $ idris_crash "applyUnfoldNu(SignatureVarElim)"
    applyUnfoldNuHelper sig omega (OmegaVarElim str x) r = Left r
    applyUnfoldNuHelper sig omega (TyEqTy x y) r = Left r
    applyUnfoldNuHelper sig omega (ElEqTy x y z) r = Left r
    applyUnfoldNuHelper sig omega (TyEqVal _) r = Left r
    applyUnfoldNuHelper sig omega (ElEqVal _ _) r = Left r
    applyUnfoldNuHelper sig omega ZeroTy r = Left r
    applyUnfoldNuHelper sig omega OneTy r = Left r
    applyUnfoldNuHelper sig omega OneVal r = Left r
    applyUnfoldNuHelper sig omega (ZeroElim ty x) r = Left r

    public export
    applyUnfold : Signature -> Omega -> SnocList VarName -> Elem -> OpFreeTerm -> Either Range Elem
    applyUnfold sig omega ctx t p = Prelude.do
      applyUnfoldNu sig omega ctx (openEval sig omega t) p
