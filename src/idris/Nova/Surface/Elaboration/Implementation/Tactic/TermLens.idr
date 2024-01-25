module Nova.Surface.Elaboration.Implementation.Tactic.TermLens

import Data.Location
import Data.String

import Text.PrettyPrint.Prettyprinter

import Nova.Core.Evaluation
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Pretty

import Nova.Surface.Elaboration.Interface
import Nova.Surface.Language

-- This module contains a procedure that given a term (Type or Elem)
-- and a path, which specifies exactly one sub-term, constructs a lens (a getter and a setter) focused on the sub-term specified by the path.

public export
data Index = IType | IElem

public export
interp : Index -> Type
interp IType = Typ
interp IElem = Elem

public export
record Lens (0 over : Index) where
  constructor MkLens
  ||| Range of the ☐ of the path
  range : Range
  ||| Context of the focused term. Guaranteed to be an extension of the original one.
  ||| TODO: Ideally we should accumulate the extension rather than full context.
  context : Context
  lens : Either (Typ, Typ -> interp over) (Elem, Elem -> interp over)

public export
postcomposeSetter : Lens over -> (interp over -> interp over') -> Lens over'
postcomposeSetter (MkLens r gamma (Left (get, set))) f = MkLens r gamma (Left (get, f . set))
postcomposeSetter (MkLens r gamma (Right (get, set))) f = MkLens r gamma (Right (get, f . set))

public export
here : {over : _} -> Range -> Context -> interp over -> Lens over
here {over = IType} r gamma x = MkLens r gamma (Left (x, id))
here {over = IElem} r gamma x = MkLens r gamma (Right (x, id))

mutual
  namespace Typ
    public export
    lensNu : Params
          => Signature
          -> Omega
          -> Context
          -> Typ
          -> OpFreeTerm
          -> M (Either (Range, Doc Ann) (Lens IType))
    lensNu sig omega gamma el (App _ (Tm _ tm) []) = MEither.do
      lens sig omega gamma el tm
    lensNu sig omega gamma (El el) path = MEither.do
      l <- Elem.lens sig omega gamma el path
      return (postcomposeSetter l El)
    lensNu sig omega gamma (PiTy x dom cod) (PiTy r _ pdom (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma dom pdom
      return (postcomposeSetter l (\dom => PiTy x dom cod))
    lensNu sig omega gamma (PiTy x dom cod) (FunTy r pdom (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma dom pdom
      return (postcomposeSetter l (\dom => PiTy x dom cod))
    lensNu sig omega gamma (PiTy x dom cod) (PiTy r _ (App _ (Underscore _) []) pcod) = MEither.do
      l <- lens sig omega (gamma :< (x, dom)) cod pcod
      return (postcomposeSetter l (\cod => PiTy x dom cod))
    lensNu sig omega gamma (PiTy x dom cod) (FunTy r (App _ (Underscore _) []) pcod) = MEither.do
      l <- lens sig omega (gamma :< (x, dom)) cod pcod
      return (postcomposeSetter l (\cod => PiTy x dom cod))
    lensNu sig omega gamma (PiTy x dom cod) p = error (range p, "Failing at (_ : _) →")
    lensNu sig omega gamma (ImplicitPiTy x dom cod) (ImplicitPiTy r _ pdom (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma dom pdom
      return (postcomposeSetter l (\dom => ImplicitPiTy x dom cod))
    lensNu sig omega gamma (ImplicitPiTy x dom cod) (ImplicitPiTy r _ (App _ (Underscore _) []) pcod) = MEither.do
      l <- lens sig omega (gamma :< (x, dom)) cod pcod
      return (postcomposeSetter l (\cod => ImplicitPiTy x dom cod))
    lensNu sig omega gamma (ImplicitPiTy x dom cod) p = error (range p, "Failing at {_ : _} →")
    lensNu sig omega gamma (SigmaTy x dom cod) (SigmaTy r _ pdom (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma dom pdom
      return (postcomposeSetter l (\dom => SigmaTy x dom cod))
    lensNu sig omega gamma (SigmaTy x dom cod) (SigmaTy r _ (App _ (Underscore _) []) pcod) = MEither.do
      l <- lens sig omega (gamma :< (x, dom)) cod pcod
      return (postcomposeSetter l (\cod => SigmaTy x dom cod))
    lensNu sig omega gamma (SigmaTy x dom cod) p = error (range p, "Failing at (_ : _) ⨯ _")
    -- We need to figure out how to support this.
    -- Note that the endpoint is a type!
    -- This won't work:
    --             vvv e is a type! This is ill-typed!
    -- Γ ⊦ p : e₀ ≡ e ∈ 𝕌
    -- ⟦Γ | e | ☐ | p, True⟧ = e₀
    lensNu sig omega gamma e (App r (Box _) []) = MEither.do
      error (r, "☐ unsupported at a type")
    lensNu sig omega gamma NatTy p = error (range p, "Failing at ℕ")
    lensNu sig omega gamma ZeroTy p = error (range p, "Failing at 𝟘")
    lensNu sig omega gamma OneTy p = error (range p, "Failing at 𝟙")
    lensNu sig omega gamma UniverseTy p = error (range p, "Failing at 𝕌")
    lensNu sig omega gamma (ContextSubstElim x y) f = assert_total $ idris_crash "lensNu(_[_])"
    lensNu sig omega gamma (SignatureSubstElim x y) f = assert_total $ idris_crash "lensNu(_[_])"
    lensNu sig omega gamma (OmegaVarElim {}) p = error (range p, "Failing at Ωᵢ")
    lensNu sig omega gamma (TyEqTy a b) (TyEqTy _ pa (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma a pa
      return (postcomposeSetter l (\a => TyEqTy a b))
    lensNu sig omega gamma (TyEqTy a b) (TyEqTy _ (App _ (Underscore _) []) pb) = MEither.do
      l <- lens sig omega gamma b pb
      return (postcomposeSetter l (\b => TyEqTy a b))
    lensNu sig omega gamma (TyEqTy a b) p = error (range p, "Failing at _ ≡ _ type")
    lensNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ pa (App _ (Underscore _) []) (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma a pa
      return (postcomposeSetter l (\a => ElEqTy a b ty))
    lensNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ (App _ (Underscore _) []) pb (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma b pb
      return (postcomposeSetter l (\b => ElEqTy a b ty))
    lensNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ (App _ (Underscore _) []) (App _ (Underscore _) []) pty) = MEither.do
      l <- lens sig omega gamma ty pty
      return (postcomposeSetter l (\ty => ElEqTy a b ty))
    lensNu sig omega gamma (ElEqTy a b ty) p = error (range p, "Failing at _ ≡ _ ∈ _")
    lensNu sig omega gamma (SignatureVarElim k sigma) p = error (range p, "Failing at Xᵢ")

    public export
    lens : Params => Signature -> Omega -> Context -> Typ -> OpFreeTerm -> M (Either (Range, Doc Ann) (Lens IType))
    lens sig omega gamma t p = MEither.do
      lensNu sig omega gamma !(liftM $ openEval sig omega t) p

  namespace Elem
    ||| Try applying rewrite tactic on a well-typed element
    ||| Γ ⊦ t : T
    ||| The element must be head-neutral w.r.t. open evaluation
    ||| OpFreeTerm must represent a valid path!
    ||| See Surface/Language for a description of being a valid path.
    public export
    lensNu : Params => Signature -> Omega -> Context -> Elem -> OpFreeTerm -> M (Either (Range, Doc Ann) (Lens IElem))
    lensNu sig omega gamma el (App _ (Tm _ tm) []) = MEither.do
      lens sig omega gamma el tm
    lensNu sig omega gamma (PiTy x dom cod) (PiTy r _ pdom (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma dom pdom
      return (postcomposeSetter l (\dom => PiTy x dom cod))
    lensNu sig omega gamma (PiTy x dom cod) (FunTy r pdom (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma dom pdom
      return (postcomposeSetter l (\dom => PiTy x dom cod))
    lensNu sig omega gamma (PiTy x dom cod) (PiTy r _ (App _ (Underscore _) []) pcod) = MEither.do
      l <- lens sig omega (gamma :< (x, El dom)) cod pcod
      return (postcomposeSetter l (\cod => PiTy x dom cod))
    lensNu sig omega gamma (PiTy x dom cod) (FunTy r (App _ (Underscore _) []) pcod) = MEither.do
      l <- lens sig omega (gamma :< (x, El dom)) cod pcod
      return (postcomposeSetter l (\cod => PiTy x dom cod))
    lensNu sig omega gamma (PiTy x dom cod) p = error (range p, "Failing at (_ : _) → _")
    lensNu sig omega gamma (ImplicitPiTy x dom cod) (ImplicitPiTy r _ pdom (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma dom pdom
      return (postcomposeSetter l (\dom => ImplicitPiTy x dom cod))
    lensNu sig omega gamma (ImplicitPiTy x dom cod) (ImplicitPiTy r _ (App _ (Underscore _) []) pcod) = MEither.do
      l <- lens sig omega (gamma :< (x, El dom)) cod pcod
      return (postcomposeSetter l (\cod => ImplicitPiTy x dom cod))
    lensNu sig omega gamma (ImplicitPiTy x dom cod) p = error (range p, "Failing at {_ : _} → _")
    lensNu sig omega gamma (SigmaTy x dom cod) (SigmaTy r _ pdom (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma dom pdom
      return (postcomposeSetter l (\dom => SigmaTy x dom cod))
    lensNu sig omega gamma (SigmaTy x dom cod) (SigmaTy r _ (App _ (Underscore _) []) pcod) = MEither.do
      l <- lens sig omega (gamma :< (x, El dom)) cod pcod
      return (postcomposeSetter l (\cod => SigmaTy x dom cod))
    lensNu sig omega gamma (SigmaTy x dom cod) p = error (range p, "Failing at (_ : _) ⨯ _")
    lensNu sig omega gamma (PiVal x a b body) (PiVal r _ pbody) = MEither.do
      l <- lens sig omega (gamma :< (x, a)) body pbody
      return (postcomposeSetter l (\body => PiVal x a b body))
    lensNu sig omega gamma (PiVal x a b body) p = error (range p, "_ ↦ _")
    lensNu sig omega gamma (ImplicitPiVal x a b body) (ImplicitPiVal r _ pbody) = MEither.do
      l <- lens sig omega (gamma :< (x, a)) body pbody
      return (postcomposeSetter l (\body => ImplicitPiVal x a b body))
    lensNu sig omega gamma (ImplicitPiVal x a b body) p = error (range p, "{_} ↦ _")
    lensNu sig omega gamma (SigmaVal x dom cod a b) (SigmaVal r pa (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma a pa
      return (postcomposeSetter l (\a => SigmaVal x dom cod a b))
    lensNu sig omega gamma (SigmaVal x dom cod a b) (SigmaVal r (App _ (Underscore _) []) pb) = MEither.do
      l <- lens sig omega gamma b pb
      return (postcomposeSetter l (\b => SigmaVal x dom cod a b))
    lensNu sig omega gamma (SigmaVal x dom cod a b) p = error (range p, "_, _")
    lensNu sig omega gamma e (App r (Box _) []) = MEither.do
      return (here r gamma e)
    lensNu sig omega gamma (PiElim f x a b e) (App r h es) = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error (r, "..")
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          l <- lens sig omega gamma f (App r h (cast es))
          return (postcomposeSetter l (\f => PiElim f x a b e))
        (es :< (_, Arg ([], pe))) => MEither.do
          l <- lens sig omega gamma e pe
          return (postcomposeSetter l (\e => PiElim f x a b e))
        (es :< (r, _)) => MEither.do
          error (r, "..")
    lensNu sig omega gamma (PiElim f x a b e) p = error (range p, "Failing at _ _")
    lensNu sig omega gamma (ImplicitPiElim f x a b e) (App r h es) = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error (r, "Failing at _ {_}")
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          l <- lens sig omega gamma f (App r h (cast es))
          return (postcomposeSetter l (\f => ImplicitPiElim f x a b e))
        (es :< (_, Arg ([], pe))) => MEither.do
          l <- lens sig omega gamma e pe
          return (postcomposeSetter l (\e => ImplicitPiElim f x a b e))
        (es :< (r, _)) => MEither.do
          error (r, "Failing at _ {_}")
    lensNu sig omega gamma (ImplicitPiElim f x a b e) p = error (range p, "Failing at _ {_}")
    lensNu sig omega gamma (SigmaElim1 f x a b) (App r h es) = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error (r, "Failing at _ .π₁")
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          l <- lens sig omega gamma f (App r h (cast es))
          return (postcomposeSetter l (\f => SigmaElim1 f x a b))
        (es :< (_, Pi1)) => MEither.do
          l <- lens sig omega gamma f (App r h (cast es))
          return (postcomposeSetter l (\f => SigmaElim1 f x a b))
        (es :< (r, _)) => MEither.do
          error (r, "Failing at _ .π₁")
    lensNu sig omega gamma (SigmaElim1 f x a b) p = error (range p, "Failing at _ .π₁")
    lensNu sig omega gamma (SigmaElim2 f x a b) (App r h es) = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error (r, "Failing at _ .π₂")
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          l <- lens sig omega gamma f (App r h (cast es))
          return (postcomposeSetter l (\f => SigmaElim2 f x a b))
        (es :< (_, Pi2)) => MEither.do
          l <- lens sig omega gamma f (App r h (cast es))
          return (postcomposeSetter l (\f => SigmaElim2 f x a b))
        (es :< (r, _)) => MEither.do
          error (r, "Failing at _ .π₂")
    lensNu sig omega gamma (SigmaElim2 f x a b) p = error (range p, "Failing at _ .π₂")
    lensNu sig omega gamma NatVal0 p = error (range p, "Z")
    lensNu sig omega gamma (NatVal1 t) (App r (NatVal1 _) [(_, Arg ([], p))]) = MEither.do
      l <- lens sig omega gamma t p
      return (postcomposeSetter l NatVal1)
    lensNu sig omega gamma (NatVal1 t) p = error (range p, "Failing at S _")
    lensNu sig omega gamma NatTy p = error (range p, "Failing at ℕ")
    lensNu sig omega gamma ZeroTy p = error (range p, "Failing at 𝟘")
    lensNu sig omega gamma OneTy p = error (range p, "Failing at 𝟙")
    lensNu sig omega gamma OneVal p = error (range p, "Failing at ()")
    lensNu sig omega gamma (ZeroElim ty t) (App r (ZeroElim _)
                                                       [(_, Arg ([], pt))]
                                                ) = MEither.do
      l <- lens sig omega gamma t pt
      return (postcomposeSetter l (ZeroElim ty))
    lensNu sig omega gamma (ZeroElim ty t) p = error (range p, "Failing at 𝟘")
    lensNu sig omega gamma (NatElim x schema z y h s t) (App r (NatElim _)
                                                              [(_, Arg ([], pschema)),
                                                               (_, Arg ([], pz)),
                                                               (_, Arg ([], ps)),
                                                               (_, Arg ([], pt))]
                                                         ) = MEither.do
      case (pschema, pz, ps, pt) of
        (pschema, App _ (Underscore _) [], App _ (Underscore _) [], App _ (Underscore _) []) => MEither.do
          l <- lens sig omega (gamma :< (x, NatTy)) schema pschema
          return (postcomposeSetter l (\schema => NatElim x schema z y h s t))
        (App _ (Underscore _) [], pz, App _ (Underscore _) [], App _ (Underscore _) []) => MEither.do
          l <- lens sig omega gamma z pz
          return (postcomposeSetter l (\z => NatElim x schema z y h s t))
        (App _ (Underscore _) [], App _ (Underscore _) [], ps, App _ (Underscore _) []) => MEither.do
          l <- lens sig omega (gamma :< (y, NatTy) :< (h, schema)) s ps
          return (postcomposeSetter l (\s => NatElim x schema z y h s t))
        (App _ (Underscore _) [], App _ (Underscore _) [], App _ (Underscore _) [], pt) => MEither.do
          l <- lens sig omega gamma t pt
          return (postcomposeSetter l (\t => NatElim x schema z y h s t))
        _ => error (r, "Failing at ℕ-elim")
    lensNu sig omega gamma (NatElim x schema z y h s t) p = error (range p, "Failing at ℕ-elim")
    lensNu sig omega gamma (ContextSubstElim x y) f = assert_total $ idris_crash "lensNu(_[_])"
    lensNu sig omega gamma (SignatureSubstElim x y) f = assert_total $ idris_crash "lensNu(_[_])"
    lensNu sig omega gamma (ContextVarElim k) p = error (range p, "Failing at xᵢ")
    lensNu sig omega gamma (SignatureVarElim k sigma) p = error (range p, "Failing at Xᵢ")
    lensNu sig omega gamma (OmegaVarElim str x) p = error (range p, "Failing at Ωᵢ")
    lensNu sig omega gamma (TyEqTy a b) (TyEqTy _ pa (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma a pa
      return (postcomposeSetter l (\a => TyEqTy a b))
    lensNu sig omega gamma (TyEqTy a b) (TyEqTy _ (App _ (Underscore _) []) pb) = MEither.do
      l <- lens sig omega gamma b pb
      return (postcomposeSetter l (\b => TyEqTy a b))
    lensNu sig omega gamma (TyEqTy a b) p = error (range p, "Failing at _ ≡ _ type")
    lensNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ pa (App _ (Underscore _) []) (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma a pa
      return (postcomposeSetter l (\a => ElEqTy a b ty))
    lensNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ (App _ (Underscore _) []) pb (App _ (Underscore _) [])) = MEither.do
      l <- lens sig omega gamma b pb
      return (postcomposeSetter l (\b => ElEqTy a b ty))
    lensNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ (App _ (Underscore _) []) (App _ (Underscore _) []) pty) = MEither.do
      l <- lens sig omega gamma ty pty
      return (postcomposeSetter l (\ty => ElEqTy a b ty))
    lensNu sig omega gamma (ElEqTy a b ty) p = error (range p, "Failing at _ ≡ _ ∈ _")
    lensNu sig omega gamma (TyEqVal _) p = error (range p, "Failing at Refl")
    lensNu sig omega gamma (ElEqVal _ _) p = error (range p, "Failing at Refl")

    public export
    lens : Params => Signature -> Omega -> Context -> Elem -> OpFreeTerm -> M (Either (Range, Doc Ann) (Lens IElem))
    lens sig omega gamma t p = MEither.do
      lensNu sig omega gamma !(liftM $ openEval sig omega t) p

namespace Index
  public export
  lens : {over : _} -> Params => Signature -> Omega -> Context -> interp over -> OpFreeTerm -> M (Either (Range, Doc Ann) (Lens over))
  lens {over = IElem} sig omega gamma t p = Elem.lens sig omega gamma t p
  lens {over = IType} sig omega gamma t p = Typ.lens sig omega gamma t p
