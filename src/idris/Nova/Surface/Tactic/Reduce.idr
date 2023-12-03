module Nova.Surface.Tactic.Reduce

import Data.Location
import Data.SnocList

import Nova.Core.Context
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Evaluation

import Nova.Surface.Language

-- This module contains support code for the reduce tactic

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
    applyReduceNu : Signature -> Omega -> Typ -> OpFreeTerm -> M (Either Range Typ)
    applyReduceNu sig omega el (App _ (Tm _ tm) []) = MEither.do
      applyReduce sig omega el tm
    applyReduceNu sig omega (El el) path = MEither.do
      return $ El !(applyReduce sig omega el path)
    applyReduceNu sig omega (PiTy x dom cod) (PiTy r _ pdom (App _ (Underscore _) [])) = MEither.do
      return $ PiTy x !(applyReduce sig omega dom pdom) cod
    applyReduceNu sig omega (PiTy x dom cod) (FunTy r pdom (App _ (Underscore _) [])) = MEither.do
      return $ PiTy x !(applyReduce sig omega dom pdom) cod
    applyReduceNu sig omega (PiTy x dom cod) (PiTy r _ (App _ (Underscore _) []) pcod) = MEither.do
      return $ PiTy x dom !(applyReduce sig omega cod pcod)
    applyReduceNu sig omega (PiTy x dom cod) (FunTy r (App _ (Underscore _) []) pcod) = MEither.do
      return $ PiTy x dom !(applyReduce sig omega cod pcod)
    applyReduceNu sig omega (PiTy x dom cod) p = error (range p)
    applyReduceNu sig omega (ImplicitPiTy x dom cod) (ImplicitPiTy r _ pdom (App _ (Underscore _) [])) = MEither.do
      return $ ImplicitPiTy x !(applyReduce sig omega dom pdom) cod
    applyReduceNu sig omega (ImplicitPiTy x dom cod) (ImplicitPiTy r _ (App _ (Underscore _) []) pcod) = MEither.do
      return $ ImplicitPiTy x dom !(applyReduce sig omega cod pcod)
    applyReduceNu sig omega (ImplicitPiTy x dom cod) p = error (range p)
    applyReduceNu sig omega (SigmaTy x dom cod) (SigmaTy r _ pdom (App _ (Underscore _) [])) = MEither.do
      return $ SigmaTy x !(applyReduce sig omega dom pdom) cod
    applyReduceNu sig omega (SigmaTy x dom cod) (SigmaTy r _ (App _ (Underscore _) []) pcod) = MEither.do
      return $ SigmaTy x dom !(applyReduce sig omega cod pcod)
    applyReduceNu sig omega (SigmaTy x dom cod) p = error (range p)
    applyReduceNu sig omega UniverseTy p = error (range p)
    applyReduceNu sig omega NatTy p = error (range p)
    applyReduceNu sig omega ZeroTy p = error (range p)
    applyReduceNu sig omega OneTy p = error (range p)
    applyReduceNu sig omega (ContextSubstElim x y) f = assert_total $ idris_crash "applyReduceNu(_[_])"
    applyReduceNu sig omega (SignatureSubstElim x y) f = assert_total $ idris_crash "applyReduceNu(_[_])"
    applyReduceNu sig omega (OmegaVarElim str x) p = error (range p)
    applyReduceNu sig omega (EqTy a b ty) (EqTy _ pa (App _ (Underscore _) []) (App _ (Underscore _) [])) = MEither.do
      return (EqTy !(applyReduce sig omega a pa) b ty)
    applyReduceNu sig omega (EqTy a b ty) (EqTy _ (App _ (Underscore _) []) pb (App _ (Underscore _) [])) = MEither.do
      return (EqTy a !(applyReduce sig omega b pb) ty)
    applyReduceNu sig omega (EqTy a b ty) (EqTy _ (App _ (Underscore _) []) (App _ (Underscore _) []) pty) = MEither.do
      return (EqTy a b !(applyReduce sig omega ty pty))
    applyReduceNu sig omega (EqTy a b ty) p = error (range p)

    public export
    applyReduce : Signature -> Omega -> Typ -> OpFreeTerm -> M (Either Range Typ)
    applyReduce sig omega t p = MEither.do
      applyReduceNu sig omega !(liftM $ openEval sig omega t) p

  namespace Elem
    ||| Try applying reduce tactic on a well-typed term
    ||| Γ ⊦ t : T
    ||| or
    ||| Γ ⊦ T type
    ||| The term must be head-neutral w.r.t. open evaluation
    ||| OpFreeTerm must represent a valid path!
    ||| See Surface/Language for a description of being a valid path.
    public export
    applyReduceNu : Signature -> Omega -> Elem -> OpFreeTerm -> M (Either Range Elem)
    applyReduceNu sig omega el (App _ (Tm _ tm) []) = MEither.do
      applyReduce sig omega el tm
    applyReduceNu sig omega (PiTy x dom cod) (PiTy r _ pdom (App _ (Underscore _) [])) = MEither.do
      return $ PiTy x !(applyReduce sig omega dom pdom) cod
    applyReduceNu sig omega (PiTy x dom cod) (FunTy r pdom (App _ (Underscore _) [])) = MEither.do
      return $ PiTy x !(applyReduce sig omega dom pdom) cod
    applyReduceNu sig omega (PiTy x dom cod) (PiTy r _ (App _ (Underscore _) []) pcod) = MEither.do
      return $ PiTy x dom !(applyReduce sig omega cod pcod)
    applyReduceNu sig omega (PiTy x dom cod) (FunTy r (App _ (Underscore _) []) pcod) = MEither.do
      return $ PiTy x dom !(applyReduce sig omega cod pcod)
    applyReduceNu sig omega (PiTy x dom cod) p = error (range p)
    applyReduceNu sig omega (ImplicitPiTy x dom cod) (ImplicitPiTy r _ pdom (App _ (Underscore _) [])) = MEither.do
      return $ ImplicitPiTy x !(applyReduce sig omega dom pdom) cod
    applyReduceNu sig omega (ImplicitPiTy x dom cod) (ImplicitPiTy r _ (App _ (Underscore _) []) pcod) = MEither.do
      return $ ImplicitPiTy x dom !(applyReduce sig omega cod pcod)
    applyReduceNu sig omega (ImplicitPiTy x dom cod) p = error (range p)
    applyReduceNu sig omega (SigmaTy x dom cod) (SigmaTy r _ pdom (App _ (Underscore _) [])) = MEither.do
      return $ SigmaTy x !(applyReduce sig omega dom pdom) cod
    applyReduceNu sig omega (SigmaTy x dom cod) (SigmaTy r _ (App _ (Underscore _) []) pcod) = MEither.do
      return $ SigmaTy x dom !(applyReduce sig omega cod pcod)
    applyReduceNu sig omega (SigmaTy x dom cod) p = error (range p)
    applyReduceNu sig omega (PiVal x a b body) (PiVal r _ pbody) = MEither.do
      return $ PiVal x a b !(applyReduce sig omega body pbody)
    applyReduceNu sig omega (PiVal x a b body) p = error (range p)
    applyReduceNu sig omega (ImplicitPiVal x a b body) (ImplicitPiVal r _ pbody) = MEither.do
      return $ ImplicitPiVal x a b !(applyReduce sig omega body pbody)
    applyReduceNu sig omega (ImplicitPiVal x a b body) p = error (range p)
    applyReduceNu sig omega (SigmaVal a b) (SigmaVal r pa (App _ (Underscore _) [])) = MEither.do
      return $ SigmaVal !(applyReduce sig omega a pa) b
    applyReduceNu sig omega (SigmaVal a b) (SigmaVal r (App _ (Underscore _) []) pb) = MEither.do
      return $ SigmaVal a !(applyReduce sig omega b pb)
    applyReduceNu sig omega (SigmaVal a b) p = error (range p)
    -- ⟦(x ↦ f) e | ☐⟧ = f[e/x]
    applyReduceNu sig omega (PiElim f x a b e) (App r (Box _) []) = MEither.do
      case !(liftM $ openEval sig omega f) of
        PiVal _ _ _ body => MEither.do
          return (ContextSubstElim body (Ext Id e))
        _ => error r
    applyReduceNu sig omega (PiElim f x a b e) (App r h es) = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error r
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          return $ PiElim !(applyReduce sig omega f (App r h (cast es))) x a b e
        (es :< (_, Arg ([], pe))) => MEither.do
          return $ PiElim f x a b !(applyReduce sig omega e pe)
        (es :< (r, _)) => MEither.do
          error r
    applyReduceNu sig omega (PiElim f x a b e) p = error (range p)
    -- ⟦({x} ↦ f) e | ☐⟧ = f[e/x]
    applyReduceNu sig omega (ImplicitPiElim f x a b e) (App r (Box _) []) = MEither.do
      case !(liftM $ openEval sig omega f) of
        ImplicitPiVal _ _ _ body => MEither.do
          return (ContextSubstElim body (Ext Id e))
        _ => error r
    applyReduceNu sig omega (ImplicitPiElim f x a b e) (App r h es) = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error r
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          return $ ImplicitPiElim !(applyReduce sig omega f (App r h (cast es))) x a b e
        (es :< (_, Arg ([], pe))) => MEither.do
          return $ ImplicitPiElim f x a b !(applyReduce sig omega e pe)
        (es :< (r, _)) => MEither.do
          error r
    applyReduceNu sig omega (ImplicitPiElim f x a b e) p = error (range p)
    -- ⟦(a, b) .π₁ | ☐⟧ = a
    applyReduceNu sig omega (SigmaElim1 f x a b) (App r (Box _) []) = MEither.do
      case !(liftM $ openEval sig omega f) of
        SigmaVal p q => MEither.do
          return p
        _ => error r
    applyReduceNu sig omega (SigmaElim1 f x a b) (App r h es) = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error r
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          return $ SigmaElim1 !(applyReduce sig omega f (App r h (cast es))) x a b
        (es :< (_, Pi1)) => MEither.do
          return $ SigmaElim1 !(applyReduce sig omega f (App r h (cast es))) x a b
        (es :< (r, _)) => MEither.do
          error r
    applyReduceNu sig omega (SigmaElim1 f x a b) p = error (range p)
    -- ⟦(a, b) .π₂ | ☐⟧ = b
    applyReduceNu sig omega (SigmaElim2 f x a b) (App r (Box _) []) = MEither.do
      case !(liftM $ openEval sig omega f) of
        SigmaVal p q => MEither.do
          return q
        _ => error r
    applyReduceNu sig omega (SigmaElim2 f x a b) (App r h es) = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error r
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          return $ SigmaElim2 !(applyReduce sig omega f (App r h (cast es))) x a b
        (es :< (_, Pi2)) => MEither.do
          return $ SigmaElim2 !(applyReduce sig omega f (App r h (cast es))) x a b
        (es :< (r, _)) => MEither.do
          error r
    applyReduceNu sig omega (SigmaElim2 f x a b) p = error (range p)
    applyReduceNu sig omega NatVal0 p = error (range p)
    applyReduceNu sig omega (NatVal1 t) (App r (NatVal1 _) [(_, Arg ([], p))]) = MEither.do
      return $ NatVal1 !(applyReduce sig omega t p)
    applyReduceNu sig omega (NatVal1 t) p = error (range p)
    applyReduceNu sig omega OneVal p = error (range p)
    applyReduceNu sig omega NatTy p = error (range p)
    applyReduceNu sig omega ZeroTy p = error (range p)
    applyReduceNu sig omega OneTy p = error (range p)
    applyReduceNu sig omega (ZeroElim t) p = error (range p)
    -- ⟦ℕ-elim (x. A) z (x. h. s) 0 | ☐⟧ = z
    -- ⟦ℕ-elim (x. A) z (x. h. s) (S t) | ☐⟧ = s(t/x, ℕ-elim (x. A) z (x. h. s) t/h)
    applyReduceNu sig omega (NatElim x schema z y h s t) (App r (Box _) []) = MEither.do
      case !(liftM $ openEval sig omega t) of
        NatVal0 => return z
        NatVal1 t => return (ContextSubstElim s (Ext (Ext Id t) (NatElim x schema z y h s t)))
        _ => error r
    applyReduceNu sig omega (NatElim x schema z y h s t) (App r (NatElim _)
                                                              [(_, Arg ([], pschema)),
                                                               (_, Arg ([], pz)),
                                                               (_, Arg ([], ps)),
                                                               (_, Arg ([], pt))]
                                                         ) = MEither.do
      case (pschema, pz, ps, pt) of
        (pschema, App _ (Underscore _) [], App _ (Underscore _) [], App _ (Underscore _) []) => MEither.do
          return (NatElim x !(applyReduce sig omega schema pschema) z y h s t)
        (App _ (Underscore _) [], pz, App _ (Underscore _) [], App _ (Underscore _) []) => MEither.do
          return (NatElim x schema !(applyReduce sig omega z pz) y h s t)
        (App _ (Underscore _) [], App _ (Underscore _) [], ps, App _ (Underscore _) []) => MEither.do
          return (NatElim x schema z y h !(applyReduce sig omega s ps) t)
        (App _ (Underscore _) [], App _ (Underscore _) [], App _ (Underscore _) [], pt) => MEither.do
          return (NatElim x schema z y h s !(applyReduce sig omega t pt))
        _ => error r
    applyReduceNu sig omega (NatElim x schema z y h s t) p = error (range p)
    applyReduceNu sig omega (ContextSubstElim x y) f = assert_total $ idris_crash "applyReduceNu(_[_])"
    applyReduceNu sig omega (SignatureSubstElim x y) f = assert_total $ idris_crash "applyReduceNu(_[_])"
    applyReduceNu sig omega (ContextVarElim k) p = error (range p)
    -- ⟦(Γ ⊦ χ ≔ t : A) σ | ☐⟧ = t(σ)
    applyReduceNu sig omega (SignatureVarElim x sigma) p = MEither.do
      case lookupSignature sig x of
        Just (x, LetElemEntry ctx rhs ty) =>
          return (ContextSubstElim rhs sigma)
        Just (x, _) => error (range p)
        Nothing => throw "applyReduceNu(SignatureVarElim)"
    applyReduceNu sig omega (OmegaVarElim str x) p = error (range p)
    applyReduceNu sig omega (EqTy a b ty) (EqTy _ pa (App _ (Underscore _) []) (App _ (Underscore _) [])) = MEither.do
      return (EqTy !(applyReduce sig omega a pa) b ty)
    applyReduceNu sig omega (EqTy a b ty) (EqTy _ (App _ (Underscore _) []) pb (App _ (Underscore _) [])) = MEither.do
      return (EqTy a !(applyReduce sig omega b pb) ty)
    applyReduceNu sig omega (EqTy a b ty) (EqTy _ (App _ (Underscore _) []) (App _ (Underscore _) []) pty) = MEither.do
      return (EqTy a b !(applyReduce sig omega ty pty))
    applyReduceNu sig omega (EqTy a b ty) p = error (range p)
    applyReduceNu sig omega EqVal p = error (range p)

    public export
    applyReduce : Signature -> Omega -> Elem -> OpFreeTerm -> M (Either Range Elem)
    applyReduce sig omega t p = MEither.do
      applyReduceNu sig omega !(liftM $ openEval sig omega t) p
