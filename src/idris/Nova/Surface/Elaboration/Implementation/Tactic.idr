module Nova.Surface.Elaboration.Implementation.Tactic

import Data.AVL
import Data.List
import Data.List1
import Data.SnocList
import Data.Fin
import Data.Location
import Data.String

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Context
import Nova.Core.Conversion
import Nova.Core.Evaluation
import Nova.Core.Occurrence
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Name
import Nova.Core.Pretty
import Nova.Core.Rigidity
import Nova.Core.Substitution
import Nova.Core.Unification

import Nova.Surface.Language
import Nova.Surface.Shunting
import Nova.Surface.Operator
import Nova.Surface.SemanticToken

import Nova.Surface.Elaboration.Interface
import Nova.Surface.Elaboration.Implementation.Common
import Nova.Surface.Elaboration.Implementation.Tactic.Trivial
import Nova.Surface.Elaboration.Implementation.Tactic.Unfold
import Nova.Surface.Elaboration.Pretty

mutual
  namespace Typ
    ||| Try applying rewrite tactic on a well-formed type
    ||| Γ ⊦ T type
    ||| The term must be head-neutral w.r.t. open evaluation
    ||| OpFreeTerm must represent a valid path!
    ||| See Surface/Language for a description of being a valid path.
    public export
    applyRewriteNu : Params => Signature -> Omega -> Context -> Typ -> OpFreeTerm -> SurfaceTerm -> Bool -> ElabM (Either (Range, Doc Ann) (Omega, Typ))
    applyRewriteNu sig omega gamma el (App _ (Tm _ tm) []) prf direct = MEither.do
      applyRewrite sig omega gamma el tm prf direct
    applyRewriteNu sig omega gamma (El el) p prf direct = MEither.do
      (omega, a') <- Elem.applyRewrite sig omega gamma el p prf direct
      return (omega, El a')
    applyRewriteNu sig omega gamma (PiTy x dom cod) (PiTy r _ pdom (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, dom) <- applyRewrite sig omega gamma dom pdom prf direct
      return (omega, PiTy x dom cod)
    applyRewriteNu sig omega gamma (PiTy x dom cod) (FunTy r pdom (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, dom) <- applyRewrite sig omega gamma dom pdom prf direct
      return (omega, PiTy x dom cod)
    applyRewriteNu sig omega gamma (PiTy x dom cod) (PiTy r _ (App _ (Underscore _) []) pcod) prf direct = MEither.do
      (omega, cod) <- applyRewrite sig omega (gamma :< (x, dom)) cod pcod prf direct
      return (omega, PiTy x dom cod)
    applyRewriteNu sig omega gamma (PiTy x dom cod) (FunTy r (App _ (Underscore _) []) pcod) prf direct = MEither.do
      (omega, cod) <- applyRewrite sig omega (gamma :< (x, dom)) cod pcod prf direct
      return (omega, PiTy x dom cod)
    applyRewriteNu sig omega gamma (PiTy x dom cod) p prf direct = error (range p, "Failing at (_ : _) →")
    applyRewriteNu sig omega gamma (ImplicitPiTy x dom cod) (ImplicitPiTy r _ pdom (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, dom) <- applyRewrite sig omega gamma dom pdom prf direct
      return (omega, ImplicitPiTy x dom cod)
    applyRewriteNu sig omega gamma (ImplicitPiTy x dom cod) (ImplicitPiTy r _ (App _ (Underscore _) []) pcod) prf direct = MEither.do
      (omega, cod) <- applyRewrite sig omega (gamma :< (x, dom)) cod pcod prf direct
      return (omega, ImplicitPiTy x dom cod)
    applyRewriteNu sig omega gamma (ImplicitPiTy x dom cod) p prf direct = error (range p, "Failing at {_ : _} →")
    applyRewriteNu sig omega gamma (SigmaTy x dom cod) (SigmaTy r _ pdom (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, dom) <- applyRewrite sig omega gamma dom pdom prf direct
      return (omega, SigmaTy x dom cod)
    applyRewriteNu sig omega gamma (SigmaTy x dom cod) (SigmaTy r _ (App _ (Underscore _) []) pcod) prf direct = MEither.do
      (omega, cod) <- applyRewrite sig omega (gamma :< (x, dom)) cod pcod prf direct
      return (omega, SigmaTy x dom cod)
    applyRewriteNu sig omega gamma (SigmaTy x dom cod) p prf direct = error (range p, "Failing at (_ : _) ⨯ _")
    -- We need to figure out how to support this.
    -- Note that the endpoint is a type!
    -- This won't work:
    --             vvv e is a type! This is ill-typed!
    -- Γ ⊦ p : e₀ ≡ e ∈ 𝕌
    -- ⟦Γ | e | ☐ | p, True⟧ = e₀
    applyRewriteNu sig omega gamma e (App r (Box _) []) prf b = MEither.do
      error (r, "☐ unsupport at a type")
    applyRewriteNu sig omega gamma NatTy p prf direct = error (range p, "Failing at ℕ")
    applyRewriteNu sig omega gamma ZeroTy p prf direct = error (range p, "Failing at 𝟘")
    applyRewriteNu sig omega gamma OneTy p prf direct = error (range p, "Failing at 𝟙")
    applyRewriteNu sig omega gamma UniverseTy p prf direct = error (range p, "Failing at 𝕌")
    applyRewriteNu sig omega gamma (ContextSubstElim x y) f prf direct = assert_total $ idris_crash "applyRewriteNu(_[_])"
    applyRewriteNu sig omega gamma (SignatureSubstElim x y) f prf direct = assert_total $ idris_crash "applyRewriteNu(_[_])"
    applyRewriteNu sig omega gamma (OmegaVarElim {}) p prf direct = error (range p, "Failing at Ωᵢ")
    applyRewriteNu sig omega gamma (TyEqTy a b) (TyEqTy _ pa (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, a) <- applyRewrite sig omega gamma a pa prf direct
      return (omega, TyEqTy a b)
    applyRewriteNu sig omega gamma (TyEqTy a b) (TyEqTy _ (App _ (Underscore _) []) pb) prf direct = MEither.do
      (omega, b) <- applyRewrite sig omega gamma b pb prf direct
      return (omega, TyEqTy a b)
    applyRewriteNu sig omega gamma (TyEqTy a b) p prf direct = error (range p, "Failing at _ ≡ _ type")
    applyRewriteNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ pa (App _ (Underscore _) []) (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, a) <- applyRewrite sig omega gamma a pa prf direct
      return (omega, ElEqTy a b ty)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ (App _ (Underscore _) []) pb (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, b) <- applyRewrite sig omega gamma b pb prf direct
      return (omega, ElEqTy a b ty)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ (App _ (Underscore _) []) (App _ (Underscore _) []) pty) prf direct = MEither.do
      (omega, ty) <- applyRewrite sig omega gamma ty pty prf direct
      return (omega, ElEqTy a b ty)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) p prf direct = error (range p, "Failing at _ ≡ _ ∈ _")
    applyRewriteNu sig omega gamma (SignatureVarElim k sigma) p prf direct = error (range p, "Failing at Xᵢ")

    public export
    applyRewrite : Params => Signature -> Omega -> Context -> Typ -> OpFreeTerm -> SurfaceTerm -> Bool -> ElabM (Either (Range, Doc Ann) (Omega, Typ))
    applyRewrite sig omega gamma t p prf direct = MEither.do
      applyRewriteNu sig omega gamma !(ElabEither.liftM $ openEval sig omega t) p prf direct

  namespace Elem
    ||| Try applying rewrite tactic on a well-typed element
    ||| Γ ⊦ t : T
    ||| The element must be head-neutral w.r.t. open evaluation
    ||| OpFreeTerm must represent a valid path!
    ||| See Surface/Language for a description of being a valid path.
    public export
    applyRewriteNu : Params => Signature -> Omega -> Context -> Elem -> OpFreeTerm -> SurfaceTerm -> Bool -> ElabM (Either (Range, Doc Ann) (Omega, Elem))
    applyRewriteNu sig omega gamma el (App _ (Tm _ tm) []) prf direct = MEither.do
      applyRewrite sig omega gamma el tm prf direct
    applyRewriteNu sig omega gamma (PiTy x dom cod) (PiTy r _ pdom (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, dom) <- applyRewrite sig omega gamma dom pdom prf direct
      return (omega, PiTy x dom cod)
    applyRewriteNu sig omega gamma (PiTy x dom cod) (FunTy r pdom (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, dom) <- applyRewrite sig omega gamma dom pdom prf direct
      return (omega, PiTy x dom cod)
    applyRewriteNu sig omega gamma (PiTy x dom cod) (PiTy r _ (App _ (Underscore _) []) pcod) prf direct = MEither.do
      (omega, cod) <- applyRewrite sig omega (gamma :< (x, El dom)) cod pcod prf direct
      return (omega, PiTy x dom cod)
    applyRewriteNu sig omega gamma (PiTy x dom cod) (FunTy r (App _ (Underscore _) []) pcod) prf direct = MEither.do
      (omega, cod) <- applyRewrite sig omega (gamma :< (x, El dom)) cod pcod prf direct
      return (omega, PiTy x dom cod)
    applyRewriteNu sig omega gamma (PiTy x dom cod) p prf direct = error (range p, "Failing at (_ : _) → _")
    applyRewriteNu sig omega gamma (ImplicitPiTy x dom cod) (ImplicitPiTy r _ pdom (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, dom) <- applyRewrite sig omega gamma dom pdom prf direct
      return (omega, ImplicitPiTy x dom cod)
    applyRewriteNu sig omega gamma (ImplicitPiTy x dom cod) (ImplicitPiTy r _ (App _ (Underscore _) []) pcod) prf direct = MEither.do
      (omega, cod) <- applyRewrite sig omega (gamma :< (x, El dom)) cod pcod prf direct
      return (omega, ImplicitPiTy x dom cod)
    applyRewriteNu sig omega gamma (ImplicitPiTy x dom cod) p prf direct = error (range p, "Failing at {_ : _} → _")
    applyRewriteNu sig omega gamma (SigmaTy x dom cod) (SigmaTy r _ pdom (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, dom) <- applyRewrite sig omega gamma dom pdom prf direct
      return (omega, SigmaTy x dom cod)
    applyRewriteNu sig omega gamma (SigmaTy x dom cod) (SigmaTy r _ (App _ (Underscore _) []) pcod) prf direct = MEither.do
      (omega, cod) <- applyRewrite sig omega (gamma :< (x, El dom)) cod pcod prf direct
      return (omega, SigmaTy x dom cod)
    applyRewriteNu sig omega gamma (SigmaTy x dom cod) p prf direct = error (range p, "Failing at (_ : _) ⨯ _")
    applyRewriteNu sig omega gamma (PiVal x a b body) (PiVal r _ pbody) prf direct = MEither.do
      (omega, body) <- applyRewrite sig omega (gamma :< (x, a)) body pbody prf direct
      return (omega, PiVal x a b body)
    applyRewriteNu sig omega gamma (PiVal x a b body) p prf direct = error (range p, "_ ↦ _")
    applyRewriteNu sig omega gamma (ImplicitPiVal x a b body) (ImplicitPiVal r _ pbody) prf direct = MEither.do
      (omega, body) <- applyRewrite sig omega (gamma :< (x, a)) body pbody prf direct
      return (omega, ImplicitPiVal x a b body)
    applyRewriteNu sig omega gamma (ImplicitPiVal x a b body) p prf direct = error (range p, "{_} ↦ _")
    applyRewriteNu sig omega gamma (SigmaVal x dom cod a b) (SigmaVal r pa (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, a) <- applyRewrite sig omega gamma a pa prf direct
      return (omega, SigmaVal x dom cod a b)
    applyRewriteNu sig omega gamma (SigmaVal x dom cod a b) (SigmaVal r (App _ (Underscore _) []) pb) prf direct = MEither.do
      (omega, b) <- applyRewrite sig omega gamma b pb prf direct
      return (omega, SigmaVal x dom cod a b)
    applyRewriteNu sig omega gamma (SigmaVal x dom cod a b) p prf direct = error (range p, "_, _")
    -- Γ ⊦ p : e₀ ≡ e ∈ A
    -- ⟦Γ | e | ☐ | p, True⟧ = e₀
    applyRewriteNu sig omega gamma e (App r (Box _) []) prf True = MEither.do
      (omega, ty') <- liftUnifyM' $ newTypeMeta omega gamma SolveByUnification
      (omega, e0') <- liftUnifyM' $ newElemMeta omega gamma (OmegaVarElim ty' Id) SolveByUnification
      (omega, prf') <- liftUnifyM' $ newElemMeta omega gamma (ElEqTy (OmegaVarElim e0' Id) e (OmegaVarElim ty' Id)) SolveByElaboration
      case !(mapResult Right (Interface.solve sig omega [ElemElaboration gamma prf prf' (ElEqTy (OmegaVarElim e0' Id) e (OmegaVarElim ty' Id))])) of
        Success omega => MEither.do
          return (omega, OmegaVarElim e0' Id)
        Stuck omega [] cons =>
          return (omega, OmegaVarElim e0' Id)
        Stuck omega elabs cons => MEither.do
          {- write "rewrite failed at ☐, got stuck elaborations:" <&> Right
          doc <- ElabEither.liftM $ pretty sig (Stuck omega elabs cons)
          write (renderDocTerm doc) <&> Right -}
          error (r, "..")
        Error omega (Left err) => MEither.do
          {- let err = ElaborationError omega err
          write "rewrite failed at ☐:" <&> Right
          write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right -}
          error (r, "..")
        Error omega (Right err) => MEither.do
          {- let err = UnificationError omega err
          write "rewrite failed at ☐:" <&> Right
          write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right -}
          error (r, "..")
    -- Γ ⊦ p : e ≡ e₀ ∈ A
    -- ⟦Γ | e | ☐ | p, False⟧ = e₀
    applyRewriteNu sig omega gamma e (App r (Box _) []) prf False = MEither.do
      (omega, ty') <- liftUnifyM' $ newTypeMeta omega gamma SolveByUnification
      (omega, e0') <- liftUnifyM' $ newElemMeta omega gamma (OmegaVarElim ty' Id) SolveByUnification
      (omega, prf') <- liftUnifyM' $ newElemMeta omega gamma (ElEqTy e (OmegaVarElim e0' Id) (OmegaVarElim ty' Id)) SolveByElaboration
      case !(mapResult Right (Interface.solve sig omega [ElemElaboration gamma prf prf' (ElEqTy e (OmegaVarElim e0' Id) (OmegaVarElim ty' Id))])) of
        Success omega => MEither.do
          return (omega, OmegaVarElim e0' Id)
        Stuck omega [] cons =>
          return (omega, OmegaVarElim e0' Id)
        Stuck omega elabs cons => MEither.do
          {- write "rewrite⁻¹ failed at ☐, got stuck elaborations:" <&> Right
          doc <- ElabEither.liftM $ pretty sig (Stuck omega elabs cons)
          write (renderDocTerm doc) <&> Right -}
          error (r, "..")
        Error omega (Left err) => MEither.do
          {- let err = ElaborationError omega err
          write "rewrite⁻¹ failed at ☐:" <&> Right
          write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right -}
          error (r, "..")
        Error omega (Right err) => MEither.do
          {- let err = UnificationError omega err
          write "rewrite⁻¹ failed at ☐:" <&> Right
          write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right -}
          error (r, "..")
    applyRewriteNu sig omega gamma (PiElim f x a b e) (App r h es) prf direct = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error (r, "..")
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          (omega, f) <- applyRewrite sig omega gamma f (App r h (cast es)) prf direct
          return (omega, PiElim f x a b e)
        (es :< (_, Arg ([], pe))) => MEither.do
          (omega, e) <- applyRewrite sig omega gamma e pe prf direct
          return (omega, PiElim f x a b e)
        (es :< (r, _)) => MEither.do
          error (r, "..")
    applyRewriteNu sig omega gamma (PiElim f x a b e) p prf direct = error (range p, "Failing at _ _")
    applyRewriteNu sig omega gamma (ImplicitPiElim f x a b e) (App r h es) prf direct = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error (r, "Failing at _ {_}")
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          (omega, f) <- applyRewrite sig omega gamma f (App r h (cast es)) prf direct
          return (omega, ImplicitPiElim f x a b e)
        (es :< (_, Arg ([], pe))) => MEither.do
          (omega, e) <- applyRewrite sig omega gamma e pe prf direct
          return (omega, ImplicitPiElim f x a b e)
        (es :< (r, _)) => MEither.do
          error (r, "Failing at _ {_}")
    applyRewriteNu sig omega gamma (ImplicitPiElim f x a b e) p prf direct = error (range p, "Failing at _ {_}")
    applyRewriteNu sig omega gamma (SigmaElim1 f x a b) (App r h es) prf direct = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error (r, "Failing at _ .π₁")
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          (omega, f) <- applyRewrite sig omega gamma f (App r h (cast es)) prf direct
          return (omega, SigmaElim1 f x a b)
        (es :< (_, Pi1)) => MEither.do
          (omega, f) <- applyRewrite sig omega gamma f (App r h (cast es)) prf direct
          return (omega, SigmaElim1 f x a b)
        (es :< (r, _)) => MEither.do
          error (r, "Failing at _ .π₁")
    applyRewriteNu sig omega gamma (SigmaElim1 f x a b) p prf direct = error (range p, "Failing at _ .π₁")
    applyRewriteNu sig omega gamma (SigmaElim2 f x a b) (App r h es) prf direct = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error (r, "Failing at _ .π₂")
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          (omega, f) <- applyRewrite sig omega gamma f (App r h (cast es)) prf direct
          return (omega, SigmaElim2 f x a b)
        (es :< (_, Pi2)) => MEither.do
          (omega, f) <- applyRewrite sig omega gamma f (App r h (cast es)) prf direct
          return (omega, SigmaElim2 f x a b)
        (es :< (r, _)) => MEither.do
          error (r, "Failing at _ .π₂")
    applyRewriteNu sig omega gamma (SigmaElim2 f x a b) p prf direct = error (range p, "Failing at _ .π₂")
    applyRewriteNu sig omega gamma NatVal0 p prf direct = error (range p, "Z")
    applyRewriteNu sig omega gamma (NatVal1 t) (App r (NatVal1 _) [(_, Arg ([], p))]) prf direct = MEither.do
      (omega, t) <- applyRewrite sig omega gamma t p prf direct
      return (omega, NatVal1 t)
    applyRewriteNu sig omega gamma (NatVal1 t) p prf direct = error (range p, "Failing at S _")
    applyRewriteNu sig omega gamma NatTy p prf direct = error (range p, "Failing at ℕ")
    applyRewriteNu sig omega gamma ZeroTy p prf direct = error (range p, "Failing at 𝟘")
    applyRewriteNu sig omega gamma OneTy p prf direct = error (range p, "Failing at 𝟙")
    applyRewriteNu sig omega gamma OneVal p prf direct = error (range p, "Failing at ()")
    applyRewriteNu sig omega gamma (ZeroElim ty t) (App r (ZeroElim _)
                                                       [(_, Arg ([], pt))]
                                                ) prf direct = MEither.do
      (omega, t) <- applyRewrite sig omega gamma t pt prf direct
      return (omega, ZeroElim ty t)
    applyRewriteNu sig omega gamma (ZeroElim ty t) p prf direct = error (range p, "Failing at 𝟘")
    applyRewriteNu sig omega gamma (NatElim x schema z y h s t) (App r (NatElim _)
                                                              [(_, Arg ([], pschema)),
                                                               (_, Arg ([], pz)),
                                                               (_, Arg ([], ps)),
                                                               (_, Arg ([], pt))]
                                                         ) prf direct = MEither.do
      case (pschema, pz, ps, pt) of
        (pschema, App _ (Underscore _) [], App _ (Underscore _) [], App _ (Underscore _) []) => MEither.do
          (omega, schema) <- applyRewrite sig omega (gamma :< (x, NatTy)) schema pschema prf direct
          return (omega, NatElim x schema z y h s t)
        (App _ (Underscore _) [], pz, App _ (Underscore _) [], App _ (Underscore _) []) => MEither.do
          (omega, z) <- applyRewrite sig omega gamma z pz prf direct
          return (omega, NatElim x schema z y h s t)
        (App _ (Underscore _) [], App _ (Underscore _) [], ps, App _ (Underscore _) []) => MEither.do
          (omega, s) <- applyRewrite sig omega (gamma :< (y, NatTy) :< (h, schema)) s ps prf direct
          return (omega, NatElim x schema z y h s t)
        (App _ (Underscore _) [], App _ (Underscore _) [], App _ (Underscore _) [], pt) => MEither.do
          (omega, t) <- applyRewrite sig omega gamma t pt prf direct
          return (omega, NatElim x schema z y h s t)
        _ => error (r, "Failing at ℕ-elim")
    applyRewriteNu sig omega gamma (NatElim x schema z y h s t) p prf direct = error (range p, "Failing at ℕ-elim")
    applyRewriteNu sig omega gamma (ContextSubstElim x y) f prf direct = assert_total $ idris_crash "applyRewriteNu(_[_])"
    applyRewriteNu sig omega gamma (SignatureSubstElim x y) f prf direct = assert_total $ idris_crash "applyRewriteNu(_[_])"
    applyRewriteNu sig omega gamma (ContextVarElim k) p prf direct = error (range p, "Failing at xᵢ")
    applyRewriteNu sig omega gamma (SignatureVarElim k sigma) p prf direct = error (range p, "Failing at Xᵢ")
    applyRewriteNu sig omega gamma (OmegaVarElim str x) p prf direct = error (range p, "Failing at Ωᵢ")
    applyRewriteNu sig omega gamma (TyEqTy a b) (TyEqTy _ pa (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, a) <- applyRewrite sig omega gamma a pa prf direct
      return (omega, TyEqTy a b)
    applyRewriteNu sig omega gamma (TyEqTy a b) (TyEqTy _ (App _ (Underscore _) []) pb) prf direct = MEither.do
      (omega, b) <- applyRewrite sig omega gamma b pb prf direct
      return (omega, TyEqTy a b)
    applyRewriteNu sig omega gamma (TyEqTy a b) p prf direct = error (range p, "Failing at _ ≡ _ type")
    applyRewriteNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ pa (App _ (Underscore _) []) (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, a) <- applyRewrite sig omega gamma a pa prf direct
      return (omega, ElEqTy a b ty)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ (App _ (Underscore _) []) pb (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, b) <- applyRewrite sig omega gamma b pb prf direct
      return (omega, ElEqTy a b ty)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ (App _ (Underscore _) []) (App _ (Underscore _) []) pty) prf direct = MEither.do
      (omega, ty) <- applyRewrite sig omega gamma ty pty prf direct
      return (omega, ElEqTy a b ty)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) p prf direct = error (range p, "Failing at _ ≡ _ ∈ _")
    applyRewriteNu sig omega gamma (TyEqVal _) p prf direct = error (range p, "Failing at Refl")
    applyRewriteNu sig omega gamma (ElEqVal _ _) p prf direct = error (range p, "Failing at Refl")

    public export
    applyRewrite : Params => Signature -> Omega -> Context -> Elem -> OpFreeTerm -> SurfaceTerm -> Bool -> ElabM (Either (Range, Doc Ann) (Omega, Elem))
    applyRewrite sig omega gamma t p prf direct = MEither.do
      applyRewriteNu sig omega gamma !(ElabEither.liftM $ openEval sig omega t) p prf direct

Nova.Surface.Elaboration.Interface.elabTactic sig omega (Id r) target = M.do
  write (renderDocTerm !(Elab.liftM $ prettySignature sig omega target))
  return (Right (omega, target, id))
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Trivial r) [< (x, ElemEntry ctx ty)] = M.do
  case !(Elab.liftM $ applyTrivial sig omega ty) of
    Just done => return (Right (omega, [<], \_ => [< ElemEntryInstance done]))
    Nothing => return (Left "Can't apply 'trivial'")
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Trivial r) _ = M.do
  return (Left "Wrong signature for tactic: 'trivial'")
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Composition r (alpha ::: [])) target = M.do
  Nova.Surface.Elaboration.Interface.elabTactic sig omega alpha target
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Composition r (alpha ::: beta :: gammas)) target = M.do
  Right (omega, alphaSource, alphaInterp) <- Nova.Surface.Elaboration.Interface.elabTactic sig omega alpha target
    | Left err => return (Left err)
  Right (omega, source, restInterp) <- Nova.Surface.Elaboration.Interface.elabTactic sig omega (Composition r (beta ::: gammas)) alphaSource
    | Left err => return (Left err)
  return (Right (omega, source, restInterp . alphaInterp))
-- ⟦unfold ρ⟧ : ε (Γ ⊦ B) ⇒ ε (Γ ⊦ A)
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Unfold r path) [< (x, ElemEntry ctx ty)] = M.do
 Right ty' <- Elab.liftM $ applyUnfold sig omega (map fst ctx) ty path
   | Left r => --FIX: use the range
               return (Left "Can't apply 'unfold', range: \{show r}, ρ: \{show path}")
 return (Right (omega, [< (x, ElemEntry ctx ty')], id))
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Unfold r path) _ = return (Left "Target context is empty or its last entry is a let")
Nova.Surface.Elaboration.Interface.elabTactic sig omega (RewriteInv r path prf) [< (x, ElemEntry ctx ty)] = M.do
  case !(applyRewrite sig omega ctx ty path prf False) of
    Left r0 => M.do
      -- write "Rewrite⁻¹ failed at \{show r0}"
      return (Left "rewrite⁻¹ failed at \{show r0}")
    Right (omega, ty0) => return (Right (omega, [< (x, ElemEntry ctx ty0)], id))
Nova.Surface.Elaboration.Interface.elabTactic sig omega (RewriteInv r path prf) target = MEither.do
  error "Wrong context for rewrite⁻¹"
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Rewrite r path prf) [< (x, ElemEntry ctx ty)] = M.do
  case !(applyRewrite sig omega ctx ty path prf True) of
    Left r0 => M.do
      -- write "Rewrite failed at \{show r0}"
      return (Left "rewrite failed at \{show r0}")
    Right (omega, ty0) => return (Right (omega, [< (x, ElemEntry ctx ty0)], id))
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Rewrite r path prf) target = MEither.do
  error "Wrong context for rewrite"
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Exact r tm) [< (x, ElemEntry ctx ty)] = M.do
  (omega, m') <- liftUnifyM $ newElemMeta omega ctx ty SolveByElaboration
  case !(Interface.solve sig omega [ElemElaboration ctx tm m' ty]) of
    Success omega =>
       return (Right (omega, [<], \_ => [< ElemEntryInstance (OmegaVarElim m' Id)]))
    Stuck omega [] cons =>
       return (Right (omega, [<], \_ => [< ElemEntryInstance (OmegaVarElim m' Id)]))
    Stuck omega elabs cons => M.do
      let err = Stuck omega elabs cons
      return (Left "Stuck elaborating the exact term;\n \{renderDocNoAnn !(liftM $ pretty sig err)}")
    Error {} => return (Left "Error elaborating the exact term")
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Exact r tm) target = return (Left "Wrong target context for exact tactic")
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Split r [<] alpha) target =
  Nova.Surface.Elaboration.Interface.elabTactic sig omega alpha target
-- THOUGHT: Pretty sure Split can be generalised such that the source context is arbitrary
-- ⟦α⟧ ⇝ α' : ε ⇒ Σ
-- ⟦β⟧ ⇝ β' : ε ⇒ (Γ(id, α' ·) ⊦ A(id, α' ·))
-- --------------------------
-- ⟦* α * β⟧ ⇝ \x => α' x, β' x : ε ⇒ Σ (Γ ⊦ A)
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Split r (betas :< beta) alpha) (sigma :< (x, ElemEntry ctx ty)) = M.do
  Right (omega, [<], interpA) <- Nova.Surface.Elaboration.Interface.elabTactic sig omega (Split r betas beta) sigma
    | _ => return (Left "Error elaborating Split")
  Right (omega, [<], interpB) <- Nova.Surface.Elaboration.Interface.elabTactic sig omega alpha [< (x, ElemEntry (subst ctx (ext Id (cast (interpA [<])))) (SignatureSubstElim ty (ext Id (cast (interpA [<])))))]
    | _ => return (Left "Error elaborating Split")
  return (Right (omega, [<], \x => interpA x ++ interpB x))
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Split r (betas :< beta) alpha) target = return (Left "Wrong target context for split tactic")
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Let r x e) target =  M.do
  (omega, ty') <- liftUnifyM $ newTypeMeta omega [<] SolveByUnification
  let ty = OmegaVarElim ty' Id
  (omega, e') <- liftUnifyM $ newElemMeta omega [<] ty SolveByElaboration
  -- Σ (x ≔ t : A)
  let source = target :< (x, LetElemEntry [<] (OmegaVarElim e' Id) ty)
  let
    f : SignatureInst -> SignatureInst
    f [<] = assert_total $ idris_crash "Nova.Surface.Elaboration.Interface.elabTactic/let"
    f (ts :< t) = ts
  case !(Interface.solve sig omega [ElemElaboration [<] e e' ty]) of
    Success omega => M.do
      return (Right (omega, source, f))
                --FIX:
    Stuck omega [] [] =>
      case (containsNamedHolesOnly omega) of
        True => M.do
          return (Right (omega, source, f))
        False => return (Left "Stuck elaborating exact term; have some unsolved holes: \{renderDocNoAnn !(Elab.liftM $ prettyOmega sig omega)}" )
    Stuck omega elabs cons => M.do
      let err = Stuck omega elabs cons
      return (Left "Stuck elaborating RHS of let;\n \{renderDocNoAnn !(liftM $ pretty sig err)}")
    Error {} => return (Left "Error elaborating RHS of let")
Nova.Surface.Elaboration.Interface.elabTactic sig omega (NormaliseCommutativeMonoid {}) _ = M.do
  return (Left "Not implemented yet")
