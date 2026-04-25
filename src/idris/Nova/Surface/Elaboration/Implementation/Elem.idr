module Nova.Surface.Elaboration.Implementation.Elem

import Me.Russoul.Data.Location

import Nova.Control.Monad.Id
import Nova.Control.Monad.St
import Nova.Control.Monad.StEither

import Data.AVL
import Data.List
import Data.List1
import Data.SnocList
import Data.Fin
import Data.String

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Context
import Nova.Core.Conversion
import Nova.Core.Evaluation
import Nova.Core.Occurrence
import Nova.Core.Language
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

||| Σ Ω Γ ⊦ ⟦t⟧ ⇝ p : A
||| A is head-neutral w.r.t. open evaluation.
||| This function is not supposed to match on the type!
public export
elabElemNuOtherwise : Params
                   => SnocList Operator
                   -> Signature
                   -> Omega
                   -> Context
                   -> SurfaceTerm
                   -> OmegaName
                   -> CoreTyp
                   -> ElabM Elaboration.Result
elabElemNuOtherwise ops sig omega ctx tm@(PiTy r x dom cod) meta ty = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
  pure (Success omega [ElemElaboration ctx tm meta UniverseTy])
elabElemNuOtherwise ops sig omega ctx tm@(ImplicitPiTy r x dom cod) meta ty = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
  pure (Success omega [ElemElaboration ctx tm meta UniverseTy])
elabElemNuOtherwise ops sig omega ctx tm@(SigmaTy r x dom cod) meta ty = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
  pure (Success omega [ElemElaboration ctx tm meta UniverseTy])
elabElemNuOtherwise ops sig omega ctx tm@(FunTy x y z) meta ty = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
  pure (Success omega [ElemElaboration ctx tm meta UniverseTy])
elabElemNuOtherwise ops sig omega ctx tm@(ProdTy x y z) meta ty = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
  pure (Success omega [ElemElaboration ctx tm meta UniverseTy])
elabElemNuOtherwise ops sig omega ctx tm@(TyEqTy r a b) meta ty = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
  pure (Success omega [ElemElaboration ctx tm meta UniverseTy])
elabElemNuOtherwise ops sig omega ctx tm@(ElEqTy r a b t) meta ty = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
  pure (Success omega [ElemElaboration ctx tm meta UniverseTy])
elabElemNuOtherwise ops sig omega ctx tm@(PiVal r x f) meta ty = St.do
  (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom Id)) SolveByUnification
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty (PiTy x (OmegaVarElim dom Id) (OmegaVarElim cod Id)))
  pure (Success omega [ElemElaboration ctx tm meta (PiTy x (OmegaVarElim dom Id) (OmegaVarElim cod Id))])
elabElemNuOtherwise ops sig omega ctx tm@(ImplicitPiVal r x f) meta ty = St.do
  (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom Id)) SolveByUnification
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty (ImplicitPiTy x (OmegaVarElim dom Id) (OmegaVarElim cod Id)))
  pure (Success omega [ElemElaboration ctx tm meta (ImplicitPiTy x (OmegaVarElim dom Id) (OmegaVarElim cod Id))])
elabElemNuOtherwise ops sig omega ctx tm@(SigmaVal r a b) meta ty = St.do
  (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< ("_", OmegaVarElim dom Id)) SolveByUnification
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)))
  pure (Success omega [ElemElaboration ctx tm meta (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))])
elabElemNuOtherwise ops sig omega ctx (App r (Var r0 x) es) meta ty = St.do
  case lookupContext ctx x of
    Just (vTm, vTy) => St.do
      addSemanticToken (r0, BoundVarAnn)
      pure (Success omega [ElemElimElaboration ctx vTm vTy es meta ty])
    Nothing =>
      case lookupElemSignature sig x of
        Just ([<], idx, vTy) => St.do
          addSemanticToken (r0, ElimAnn)
          pure (Success omega [ElemElimElaboration ctx (SignatureVarElim idx Terminal) vTy es meta ty])
        Just (sigCtx, idx, ty) =>
          St.pure (Error "Non-empty signature context not supported yet for name: \{x}")
        Nothing =>
          case lookup x omega of
            Just (LetElem [<] _ vTy) => St.do
              addSemanticToken (r0, ElimAnn)
              pure (Success omega [ElemElimElaboration ctx (OmegaVarElim x Terminal) vTy es meta ty])
            _ => St.pure (Error "Undefined name: \{x}")
elabElemNuOtherwise ops sig omega ctx tm@(App r (NatVal0 x) []) meta ty = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty NatTy)
  pure (Success omega [ElemElaboration ctx tm meta NatTy])
elabElemNuOtherwise ops sig omega ctx (App r (NatVal0 x) (_ :: _)) meta ty =
  St.pure (Error "Z applied to a spine")
elabElemNuOtherwise ops sig omega ctx tm@(App r (OneVal x) []) meta ty = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty OneTy)
  pure (Success omega [ElemElaboration ctx tm meta OneTy])
elabElemNuOtherwise ops sig omega ctx (App r (OneVal x) (_ :: _)) meta ty =
  St.pure (Error "tt applied to a spine")
elabElemNuOtherwise ops sig omega ctx tm@(App r (NatVal1 _) [t]) meta ty = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty NatTy)
  pure (Success omega [ElemElaboration ctx tm meta NatTy])
elabElemNuOtherwise ops sig omega ctx (App r (NatVal1 x) _) meta ty =
  St.pure (Error "S applied to a wrong number of arguments")
elabElemNuOtherwise ops sig omega ctx (App r (NatElim _) ((_, Arg ([x], schema)) :: (_, Arg ([], z)) :: (_, Arg ([y, h], s)) :: (_, Arg ([], t)) :: es)) meta ty = St.do
  (omega, schema') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, NatTy)) SolveByElaboration
  (omega, z') <- liftUnifyM $ newElemMeta omega ctx (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)) SolveByElaboration
  (omega, s') <- liftUnifyM $ newElemMeta omega (ctx :< (y, NatTy) :< (h, OmegaVarElim schema' Id))
                                  (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))) SolveByElaboration
  (omega, t') <- liftUnifyM $ newElemMeta omega ctx NatTy SolveByElaboration
  pure (Success omega [TypeElaboration (ctx :< (x, NatTy)) schema schema',
                         ElemElaboration ctx z z' (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)),
                         ElemElaboration (ctx :< (y, NatTy) :< (h, OmegaVarElim schema' Id)) s s' (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))),
                         ElemElaboration ctx t t' NatTy,
                         ElemElimElaboration ctx (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) (OmegaVarElim t' Id)) (OmegaVarElim schema' (Ext Id (OmegaVarElim t' Id))) es meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (NatElim _) _) meta ty =
  St.pure (Error "ℕ-elim applied to a wrong number of arguments")
elabElemNuOtherwise ops sig omega ctx (App r (ZeroElim _) ((_, Arg ([], t)) :: es)) meta ty = St.do
  (omega, t') <- liftUnifyM $ newElemMeta omega ctx ZeroTy SolveByElaboration
  pure (Success omega [ElemElaboration ctx t t' ZeroTy,
                         ElemElimElaboration ctx (ZeroElim ty (OmegaVarElim t' Id)) ty es meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (ZeroElim _) _) meta ty =
  St.pure (Error "𝟘-elim applied to a wrong number of arguments")
elabElemNuOtherwise ops sig omega ctx (App _ (EqElim _) ((_, Arg ([], elemTy)) :: (_, Arg ([], a0)) :: (_, Arg ([x, h], schema)) :: (_, Arg ([], r)) :: (_, Arg ([], a1)) :: (_, Arg ([], e)) :: es)) meta ty = St.do
  (omega, t') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
  (omega, schema') <- liftUnifyM $ newTypeMeta omega ((ctx :< (x, OmegaVarElim t' Id)) :< (h, ElEqTy (ContextSubstElim (OmegaVarElim a' Id) Wk) CtxVar (ContextSubstElim (OmegaVarElim t' Id) Wk))) SolveByElaboration
  (omega, r') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim schema' (Ext (Ext Id (OmegaVarElim a' Id)) (ElEqVal (OmegaVarElim t' Id) (OmegaVarElim a' Id)))) SolveByElaboration
  (omega, e') <- liftUnifyM $ newElemMeta omega ctx (ElEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) (OmegaVarElim t' Id)) SolveByElaboration
  pure (Success omega [TypeElaboration ctx elemTy t',
                         ElemElaboration ctx a0 a' (OmegaVarElim t' Id),
                         ElemElaboration ctx a1 b' (OmegaVarElim t' Id),
                         ElemElaboration ctx e e' (ElEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) (OmegaVarElim t' Id)),
                         TypeElaboration (ctx :< (x, OmegaVarElim t' Id) :< (h, (ElEqTy (ContextSubstElim (OmegaVarElim a' Id) Wk) CtxVar (ContextSubstElim (OmegaVarElim t' Id) Wk)))) schema schema',
                         ElemElaboration ctx r r' (OmegaVarElim schema' (Ext (Ext Id (OmegaVarElim a' Id)) (ElEqVal (OmegaVarElim t' Id) (OmegaVarElim a' Id)))),
                         ElemElimElaboration ctx (OmegaVarElim r' Id) (OmegaVarElim schema' (Ext (Ext Id (OmegaVarElim b' Id)) (OmegaVarElim e' Id))) es meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (EqElim x) _) meta ty =
  St.pure (Error "J applied to a wrong number of arguments")
elabElemNuOtherwise ops sig omega ctx tm@(App r (EqVal x) []) meta ty = St.do
  -- We can have one of:
  --   ⟦Refl⟧ : (? ≡ ? ∈ ?)
  --   ⟦Refl⟧ : (? ≡ ? type)
  -- Can't decide yet
  pure (Stuck "Refl : _")
  {- (omega, t') <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByUnification
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByUnification
  let t = OmegaVarElim t' Id
  let a = OmegaVarElim a' Id
  let b = OmegaVarElim b' Id
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty (EqTy a b t))
  pure (Success omega [ElemElaboration ctx tm meta (EqTy a b t)]) -}
elabElemNuOtherwise ops sig omega ctx (App r (EqVal x) _) meta ty = St.do
  St.pure (Error "Refl applied to wrong number of arguments")
elabElemNuOtherwise ops sig omega ctx tm@(App r (NatTy x) []) meta ty = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
  pure (Success omega [ElemElaboration ctx tm meta UniverseTy])
elabElemNuOtherwise ops sig omega ctx (App r (NatTy x) _) meta ty =
  St.pure (Error "ℕ applied to a wrong number of arguments")
elabElemNuOtherwise ops sig omega ctx tm@(App r (ZeroTy x) []) meta ty = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
  pure (Success omega [ElemElaboration ctx tm meta UniverseTy])
elabElemNuOtherwise ops sig omega ctx (App r (ZeroTy x) _) meta ty =
  St.pure (Error "𝟘 applied to a wrong number of arguments")
elabElemNuOtherwise ops sig omega ctx tm@(App r (OneTy x) []) meta ty = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
  pure (Success omega [ElemElaboration ctx tm meta UniverseTy])
elabElemNuOtherwise ops sig omega ctx (App r (OneTy x) _) meta ty =
  St.pure (Error "𝟙 applied to a wrong number of arguments")
elabElemNuOtherwise ops sig omega ctx (App r (UniverseTy x) []) meta ty =
  St.pure (Error "We don't have 𝕌 : 𝕌!")
elabElemNuOtherwise ops sig omega ctx (App r (UniverseTy x) _) meta ty =
  St.pure (Error "𝕌 applied to a wrong number of arguments")
elabElemNuOtherwise ops sig omega ctx (App r (UnnamedHole r0 Nothing) []) meta ty = St.do
  (omega, n) <- liftUnifyM $ newElemMeta omega ctx ty SolveByUnification
  let omega = Elem.instantiateByElaboration omega meta (OmegaVarElim n Id)
  St.pure (Success omega [])
elabElemNuOtherwise ops sig omega ctx (App r (UnnamedHole r0 (Just vars)) []) meta ty = St.do
  let Just regctxPrefix = pickPrefix (cast ctx) vars
    | Nothing => St.pure (Error "Invalid context prefix")
  let ctxPrefix = cast regctxPrefix
  (omega, n) <- liftUnifyM $ newElemMeta omega ctxPrefix ty SolveByUnification
  let omega = Elem.instantiateByElaboration omega meta (OmegaVarElim n (WkN (length ctx `minus` length regctxPrefix)))
  St.pure (Success omega [])
elabElemNuOtherwise ops sig omega ctx (App r (UnnamedHole x _) _) meta ty =
  St.pure (Error "? applied to arguments not supported")
elabElemNuOtherwise ops sig omega ctx (App r (Hole r0 n Nothing) es) meta ty = St.do
  case (lookup n omega) of
    Just _ => pure (Error "Hole already exists: \{n}")
    Nothing => St.do
      omega <- liftUnifyM $ newElemMeta omega ctx n ty (case solveNamedHoles %search of False => NoSolve; True => SolveByUnification)
      let omega = Elem.instantiateByElaboration omega meta (OmegaVarElim n Id)
      St.Maybe.for_ (the Params %search).absFilePath (\path => addNamedHole path r0 n)
      pure (Success omega [])
elabElemNuOtherwise ops sig omega ctx (App r (Hole r0 n (Just vars)) es) meta ty = St.do
  case (lookup n omega) of
    Just _ => pure (Error "Hole already exists: \{n}")
    Nothing => St.do
      let Just regctxPrefix = pickPrefix (cast ctx) vars
        | Nothing => St.pure (Error "Invalid context prefix")
      let ctxPrefix = cast regctxPrefix
      omega <- liftUnifyM $ newElemMeta omega ctxPrefix n ty (case solveNamedHoles %search of False => NoSolve; True => SolveByUnification)
      let omega = Elem.instantiateByElaboration omega meta (OmegaVarElim n (WkN (length ctx `minus` length regctxPrefix)))
      pure (Success omega [])
elabElemNuOtherwise ops sig omega ctx (App r (Unfold r0 x) []) meta ty = St.do
  case lookupLetElemSignature sig x of
    Just ([<], idx, vRhs, vTy) =>
      pure (Success omega [ElemElimElaboration ctx (ElEqVal vTy (SignatureVarElim idx Id)) (ElEqTy (SignatureVarElim idx Id) vRhs vTy) [] meta ty])
    Just (sigCtx, idx, vRhs, vTy) =>
      pure (Error "Non-empty signature context not supported yet for signature name: \{x}")
    Nothing =>
      case lookupLetTypeSignature sig x of
        Just ([<], idx, vRhs) =>
          pure (Success omega [ElemElimElaboration ctx (TyEqVal (SignatureVarElim idx Id)) (TyEqTy (SignatureVarElim idx Id) vRhs) [] meta ty])
        Just (sigCtx, idx, vRhs) =>
          pure (Error "Non-empty signature context not supported yet for signature name: \{x}")
        Nothing => pure (Error "Undefined signature name: \{x}")
elabElemNuOtherwise ops sig omega ctx (App r (Unfold r0 x) _) meta ty = St.do
  St.pure (Error "!\{x} applied to a wrong number of arguments")
-- Π-β A (x. B) (x. f) e : (x ↦ f) e ≡ f[e/x] ∈ B[e/x]
elabElemNuOtherwise ops sig omega ctx (App r (PiBeta r0) [(_, Arg ([], dom)), (_, Arg ([x'], cod)), (_, Arg ([x], f)), (_, Arg ([], e))]) meta ty = St.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
  (omega, f') <- liftUnifyM $ newElemMeta omega (ctx :< (x, OmegaVarElim dom' Id)) (OmegaVarElim cod' Id) SolveByElaboration
  (omega, e') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim dom' Id) SolveByElaboration
  pure (Success omega [TypeElaboration ctx dom dom',
                         TypeElaboration (ctx :< (x', OmegaVarElim dom' Id)) cod cod',
                         ElemElaboration (ctx :< (x, OmegaVarElim dom' Id)) f f' (OmegaVarElim cod' Id),
                         ElemElaboration ctx e e' (OmegaVarElim dom' Id),
                         ElemElimElaboration ctx
                           (ElEqVal
                             (OmegaVarElim cod' (Ext Id (OmegaVarElim e' Id)))
                             (PiElim (PiVal x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id) (OmegaVarElim f' Id))
                                     x
                                     (OmegaVarElim dom' Id)
                                     (OmegaVarElim cod' Id)
                                     (OmegaVarElim e' Id)
                             )
                           )
                           (ElEqTy
                             (PiElim (PiVal x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id) (OmegaVarElim f' Id)) x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id) (OmegaVarElim e' Id))
                             (OmegaVarElim f' (Ext Id (OmegaVarElim e' Id)))
                             (OmegaVarElim cod' (Ext Id (OmegaVarElim e' Id)))
                           )
                           [] meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (PiBeta r0) _) meta ty =
  St.pure (Error "Π-β applied to a wrong number of arguments")
-- Π-η f : (x ↦ f x) ≡ f ∈ (x : A) → B
elabElemNuOtherwise ops sig omega ctx (App r (PiEta r0) [(_, Arg ([], f))]) meta ty = St.do
  (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< ("_", OmegaVarElim dom Id)) SolveByUnification
  (omega, f') <- liftUnifyM $ newElemMeta omega ctx (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)) SolveByElaboration
  pure (Success omega [ElemElaboration ctx f f' (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)),
                         ElemElimElaboration ctx
                           (ElEqVal
                             (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))
                             (PiVal "_"
                               (OmegaVarElim dom Id)
                               (OmegaVarElim cod Id)
                               (PiElim (OmegaVarElim f' Wk) "_" (OmegaVarElim dom Wk) (OmegaVarElim cod (Under Wk)) CtxVar)
                             )
                           )
                           (ElEqTy (PiVal "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id) (PiElim (OmegaVarElim f' Wk) "_" (OmegaVarElim dom Wk) (OmegaVarElim cod (Under Wk)) CtxVar)) (OmegaVarElim f' Id) (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)))
                           [] meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (PiEta r0) _) meta ty =
  St.pure (Error "Π-η applied to a wrong number of arguments")
-- Σ-β₁ A (x. B) a b : (a , b) .π₁ ≡ a ∈ A
elabElemNuOtherwise ops sig omega ctx (App r (SigmaBeta1 r0) [(_, Arg ([], dom)), (_, Arg ([x], cod)), (_, Arg ([], a)), (_, Arg ([], b))]) meta ty = St.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim dom' Id) SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim cod' (Ext Id (OmegaVarElim a' Id))) SolveByElaboration
  pure (Success omega [TypeElaboration ctx dom dom',
                         TypeElaboration (ctx :< (x, OmegaVarElim dom' Id)) cod cod',
                         ElemElaboration ctx a a' (OmegaVarElim dom' Id),
                         ElemElaboration ctx b b' (OmegaVarElim cod' (Ext Id (OmegaVarElim a' Id))),
                         ElemElimElaboration ctx
                           (ElEqVal
                             (OmegaVarElim dom' Id)
                             (SigmaElim1
                                (SigmaVal x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id) (OmegaVarElim a' Id) (OmegaVarElim b' Id))
                                x
                                (OmegaVarElim dom' Id)
                                (OmegaVarElim cod' Id)
                             )
                           )
                           (ElEqTy (SigmaElim1 (SigmaVal x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id) (OmegaVarElim a' Id) (OmegaVarElim b' Id)) x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id)) (OmegaVarElim a' Id) (OmegaVarElim dom' Id)) [] meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (SigmaBeta1 r0) _) meta ty =
  St.pure (Error "Σ-β₁ applied to a wrong number of arguments")
-- Σ-β₂ A (x. B) a b : (a , b) .π₂ ≡ b ∈ B(a/x)
elabElemNuOtherwise ops sig omega ctx (App r (SigmaBeta2 r0) [(_, Arg ([], dom)), (_, Arg ([x], cod)), (_, Arg ([], a)), (_, Arg ([], b))]) meta ty = St.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim dom' Id) SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim cod' (Ext Id (OmegaVarElim a' Id))) SolveByElaboration
  pure (Success omega [TypeElaboration ctx dom dom',
                         TypeElaboration (ctx :< (x, OmegaVarElim dom' Id)) cod cod',
                         ElemElaboration ctx a a' (OmegaVarElim dom' Id),
                         ElemElaboration ctx b b' (OmegaVarElim cod' (Ext Id (OmegaVarElim a' Id))),
                         ElemElimElaboration ctx
                           (ElEqVal
                             (OmegaVarElim cod' (Ext Id (OmegaVarElim a' Id)))
                             (SigmaElim2
                               (SigmaVal x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id) (OmegaVarElim a' Id) (OmegaVarElim b' Id))
                               x
                               (OmegaVarElim dom' Id)
                               (OmegaVarElim cod' Id)
                             )
                           )
                           (ElEqTy (SigmaElim2 (SigmaVal x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id) (OmegaVarElim a' Id) (OmegaVarElim b' Id)) x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id)) (OmegaVarElim b' Id) (OmegaVarElim cod' (Ext Id (OmegaVarElim a' Id)))) [] meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (SigmaBeta2 r0) _) meta ty =
  St.pure (Error "Σ-β₂ applied to a wrong number of arguments")
-- Σ-η p : (p .π₁ , p .π₂) ≡ p ∈ (x : A) ⨯ B
elabElemNuOtherwise ops sig omega ctx (App r (SigmaEta r0) [(_, Arg ([], p))]) meta ty = St.do
  (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< ("_", OmegaVarElim dom Id)) SolveByUnification
  (omega, p') <- liftUnifyM $ newElemMeta omega ctx (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)) SolveByElaboration
  pure (Success omega [ElemElaboration ctx p p' (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)),
                         ElemElimElaboration ctx
                           (ElEqVal
                             (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))
                             (SigmaVal "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id) (SigmaElim1 (OmegaVarElim p' Id) "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)) (SigmaElim2 (OmegaVarElim p' Id) "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)))
                           )
                           (ElEqTy (SigmaVal "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id) (SigmaElim1 (OmegaVarElim p' Id) "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)) (SigmaElim2 (OmegaVarElim p' Id) "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))) (OmegaVarElim p' Id) (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))) [] meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (SigmaEta r0) _) meta ty =
  St.pure (Error "Σ-η applied to a wrong number of arguments")
-- ℕ-β-Z (x. A) z (y. h. s) : ℕ-elim (x. A) z (y. h. s) Z ≡ z ∈ A[Z/x]
elabElemNuOtherwise ops sig omega ctx (App r (NatBetaZ r0) ((_, Arg ([x], schema)) :: (_, Arg ([], z)) :: (_, Arg ([y, h], s)) :: [])) meta ty = St.do
  (omega, schema') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, NatTy)) SolveByElaboration
  (omega, z') <- liftUnifyM $ newElemMeta omega ctx (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)) SolveByElaboration
  (omega, s') <- liftUnifyM $ newElemMeta omega (ctx :< (y, NatTy) :< (h, OmegaVarElim schema' Id))
                                  (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))) SolveByElaboration
  pure (Success omega [TypeElaboration (ctx :< (x, NatTy)) schema schema',
                         ElemElaboration ctx z z' (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)),
                         ElemElaboration (ctx :< (y, NatTy) :< (h, OmegaVarElim schema' Id)) s s' (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))),
                         ElemElimElaboration ctx
                           (ElEqVal
                              (OmegaVarElim schema' (Ext Id NatVal0))
                              (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) NatVal0)
                           )
                           (ElEqTy (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) NatVal0) (OmegaVarElim z' Id) (OmegaVarElim schema' (Ext Id NatVal0))) [] meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (NatBetaZ r0) _) meta ty =
  St.pure (Error "ℕ-β-Z applied to a wrong number of arguments")
-- ℕ-β-S (x. A) z (y. h. s) t : ℕ-elim (x. A) z (y. h. s) (S t) ≡ s[t/x, ℕ-elim (x. A) z (y. h. s) t/h] ∈ A[S t/x]
elabElemNuOtherwise ops sig omega ctx (App r (NatBetaS r0) [(_, Arg ([x], schema)), (_, Arg ([], z)), (_, Arg ([y, h], s)), (_, Arg ([], t))]) meta ty = St.do
  (omega, schema') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, NatTy)) SolveByElaboration
  (omega, z') <- liftUnifyM $ newElemMeta omega ctx (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)) SolveByElaboration
  (omega, s') <- liftUnifyM $ newElemMeta omega ((ctx :< (y, NatTy)) :< (h, OmegaVarElim schema' Id))
                                  (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))) SolveByElaboration
  (omega, t') <- liftUnifyM $ newElemMeta omega ctx NatTy SolveByElaboration
  pure (Success omega [TypeElaboration (ctx :< (x, NatTy)) schema schema',
                         ElemElaboration ctx z z' (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)),
                         ElemElaboration (ctx :< (y, NatTy) :< (h, OmegaVarElim schema' Id)) s s' (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))),
                         ElemElaboration ctx t t' NatTy,
                         ElemElimElaboration ctx
                           (ElEqVal
                             (OmegaVarElim schema' (Ext Id (NatVal1 (OmegaVarElim t' Id))))
                             (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) (NatVal1 (OmegaVarElim t' Id)))
                           )
                           (ElEqTy (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) (NatVal1 (OmegaVarElim t' Id))) (OmegaVarElim s' (Ext (Ext Id (OmegaVarElim t' Id)) (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) (OmegaVarElim t' Id)))) (OmegaVarElim schema' (Ext Id (NatVal1 (OmegaVarElim t' Id))))) [] meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (NatBetaS r0) _) meta ty =
  St.pure (Error "ℕ-β-S applied to a wrong number of arguments")
-- 𝟙⁼ a b : a ≡ b ∈ 𝟙
elabElemNuOtherwise ops sig omega ctx (App r (OneEq r0) [(_, Arg ([], a)), (_, Arg ([], b))]) meta ty = St.do
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx OneTy SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx OneTy SolveByElaboration
  pure (Success omega [ElemElaboration ctx a a' OneTy,
                         ElemElaboration ctx b b' OneTy,
                         ElemElimElaboration ctx
                           (ElEqVal OneTy (OmegaVarElim a' Id))
                           (ElEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) OneTy) [] meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (OneEq r0) _) meta ty =
  St.pure (Error "𝟙⁼ applied to a wrong number of arguments")
-- Π⁼ (x. f) (y. g) (z. p) : (x ↦ f) ≡ (y ↦ g) ∈ (z : A) → B
elabElemNuOtherwise ops sig omega ctx (App r (PiEq r0) [(_, Arg ([x], f)), (_, Arg ([y], g)), (_, Arg ([z], p))]) meta ty = St.do
  (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< (z, OmegaVarElim dom Id)) SolveByUnification
  (omega, f') <- liftUnifyM $ newElemMeta omega (ctx :< (x, OmegaVarElim dom Id)) (OmegaVarElim cod Id) SolveByElaboration
  (omega, g') <- liftUnifyM $ newElemMeta omega (ctx :< (y, OmegaVarElim dom Id)) (OmegaVarElim cod Id) SolveByElaboration
  (omega, p') <- liftUnifyM $ newElemMeta omega (ctx :< (z, OmegaVarElim dom Id)) (ElEqTy (OmegaVarElim f' Id) (OmegaVarElim g' Id) (OmegaVarElim cod Id)) SolveByElaboration
  pure (Success omega [ElemElaboration (ctx :< (x, OmegaVarElim dom Id)) f f' (OmegaVarElim cod Id),
                         ElemElaboration (ctx :< (y, OmegaVarElim dom Id)) g g' (OmegaVarElim cod Id),
                         ElemElaboration (ctx :< (z, OmegaVarElim dom Id)) p p' (ElEqTy (OmegaVarElim f' Id) (OmegaVarElim g' Id) (OmegaVarElim cod Id)),
                         ElemElimElaboration ctx
                           (ElEqVal (PiTy z (OmegaVarElim dom Id) (OmegaVarElim cod Id))
                                    (PiVal x (OmegaVarElim dom Id) (OmegaVarElim cod Id) (OmegaVarElim f' Id))
                           )
                           (ElEqTy (PiVal x (OmegaVarElim dom Id) (OmegaVarElim cod Id) (OmegaVarElim f' Id))
                                   (PiVal y (OmegaVarElim dom Id) (OmegaVarElim cod Id) (OmegaVarElim g' Id))
                                   (PiTy z (OmegaVarElim dom Id) (OmegaVarElim cod Id))) [] meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (PiEq r0) _) meta ty =
  St.pure (Error "Π⁼ applied to a wrong number of arguments")
-- Σ⁼ a₀ b₀ a₁ b₁ a b : (a₀ , b₀) ≡ (a₁ , b₁) ∈ (_ : A) ⨯ B
elabElemNuOtherwise ops sig omega ctx (App r (SigmaEq r0) [(_, Arg ([], a0)), (_, Arg ([], b0)), (_, Arg ([], a1)), (_, Arg ([], b1)), (_, Arg ([], a)), (_, Arg ([], b))]) meta ty = St.do
  (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< ("_", OmegaVarElim dom Id)) SolveByUnification
  (omega, a0') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim dom Id) SolveByElaboration
  (omega, a1') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim dom Id) SolveByElaboration
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx (ElEqTy (OmegaVarElim a0' Id) (OmegaVarElim a1' Id) (OmegaVarElim dom Id)) SolveByElaboration
  (omega, b0') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim cod (Ext Id (OmegaVarElim a0' Id))) SolveByElaboration
  (omega, b1') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim cod (Ext Id (OmegaVarElim a1' Id))) SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (ElEqTy (OmegaVarElim b0' Id) (OmegaVarElim b1' Id) (OmegaVarElim cod (Ext Id (OmegaVarElim a1' Id)))) SolveByElaboration
  pure (Success omega [ElemElaboration ctx a0 a0' (OmegaVarElim dom Id),
                         ElemElaboration ctx a1 a1' (OmegaVarElim dom Id),
                         ElemElaboration ctx a a' (ElEqTy (OmegaVarElim a0' Id) (OmegaVarElim a1' Id) (OmegaVarElim dom Id)),
                         ElemElaboration ctx b0 b0' (OmegaVarElim cod (Ext Id (OmegaVarElim a0' Id))),
                         ElemElaboration ctx b1 b1' (OmegaVarElim cod (Ext Id (OmegaVarElim a1' Id))),
                         ElemElaboration ctx b b' (ElEqTy (OmegaVarElim b0' Id) (OmegaVarElim b1' Id) (OmegaVarElim cod (Ext Id (OmegaVarElim a1' Id)))),
                         ElemElimElaboration ctx
                           (ElEqVal
                             (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))
                             (SigmaVal "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id) (OmegaVarElim a0' Id) (OmegaVarElim b0' Id))
                           )
                           (ElEqTy (SigmaVal "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id) (OmegaVarElim a0' Id) (OmegaVarElim b0' Id))
                                   (SigmaVal "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id) (OmegaVarElim a1' Id) (OmegaVarElim b1' Id))
                                   (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))) [] meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (SigmaEq r0) _) meta ty =
  St.pure (Error "Σ⁼ applied to a wrong number of arguments")
elabElemNuOtherwise ops sig omega ctx (App r (Tm _ tm) []) meta ty = St.do
  St.pure (Success omega [ElemElaboration ctx tm meta ty])
elabElemNuOtherwise ops sig omega ctx (App r (Tm _ tm) (_ :: _)) meta ty = St.do
  St.pure (Error "Do we want to elaborate this case? There might be ambiguity in implicit resolution because we might not know the type of the head?")
  {- (omega, t) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, tm') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t Id) SolveByElaboration
  pure (Success omega [ElemElaboration ctx tm tm' (OmegaVarElim t Id),
                         ElemElimElaboration ctx (OmegaVarElim tm' Id) (OmegaVarElim t Id) es meta ty]) -}
-- Ξ Ω ⊦ ∀x ∈ Ω (x ∉ FV(Γ))
-- Ξ Ω Γ ⊦ ∀x ∈ Ω (x ∉ FV(A))
-- Given a correct tactic, success of elaborating it depends on context Γ and type A.
-- To make sure that we can approach tactics in the source in any order, we need to make sure the context and type of the tactic
-- in question can't be refined any further over time. Or in other words, they both must not contain free Ω variables.
--
-- Ξ Ω ⊦ ⟦α⟧ ⇝ α' : ε ⇒ ε (Γ ⊦ A)
-- Ξ Ω Γ ⊦ ⟦tac α⟧ ⇝ α' · : A
elabElemNuOtherwise ops sig omega ctx (Tac r alpha) meta ty = St.do
  free <- St.liftId $ freeOmegaName sig omega ctx
  let True = isEmpty free
    | False => St.pure (Stuck "Context contains free Ω variables: \{show (List.inorder free)}")
  free <- St.liftId $ freeOmegaName sig omega ty
  let True = isEmpty free
    | False => St.pure (Stuck "Type contains free Ω variables: \{show (List.inorder free)}")
  Right (omega, [<], interp) <- elabTactic ops sig omega alpha [< ("_", ElemEntry ctx ty)]
           -- FIX:        vvvvv This is inefficient! Instead we should check that Ω is okay to solve that tactic and give it exactly one try!
    | Left (r, reason) => St.pure (Stuck ("At" ++ show r ++ ", reason: " ++ renderDocTerm reason))
    | Right (_, interp) => St.pure (Error "Source signature of the tactic must be ε, but it is not.")
  let [< ElemEntryInstance solution] = interp [<]
    | _ => assert_total $ idris_crash "elabElemNuOtherwise(Tac)"
  let omega = instantiateByElaboration omega meta solution
  pure (Success omega [])
elabElemNuOtherwise ops sig omega ctx (App r (Underscore r0) _) meta ty =
  St.pure (Error "_ is not a valid term")
elabElemNuOtherwise ops sig omega ctx (App r (Box r0) _) meta ty =
  St.pure (Error "☐ is not a valid term")
elabElemNuOtherwise ops sig omega ctx (App r (El r0) _) meta ty = St.do
  St.pure (Error "El _ is not an element")

public export
elabElemNuAtUniverse : Params
                    => SnocList Operator
                    -> Signature
                    -> Omega
                    -> Context
                    -> SurfaceTerm
                    -> OmegaName
                    -> ElabM Elaboration.Result
elabElemNuAtUniverse ops sig omega ctx (PiTy r x dom cod) meta = St.do
  (omega, dom') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  (omega, cod') <- liftUnifyM $ newElemMeta omega (ctx :< (x, El $ OmegaVarElim dom' Id)) UniverseTy SolveByElaboration
  let omega = Elem.instantiateByElaboration omega meta (PiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  pure (Success omega [ElemElaboration ctx dom dom' UniverseTy, ElemElaboration (ctx :< (x, El $ OmegaVarElim dom' Id)) cod cod' UniverseTy])
elabElemNuAtUniverse ops sig omega ctx (ImplicitPiTy r x dom cod) meta = St.do
  (omega, dom') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  (omega, cod') <- liftUnifyM $ newElemMeta omega (ctx :< (x, El $ OmegaVarElim dom' Id)) UniverseTy SolveByElaboration
  let omega = Elem.instantiateByElaboration omega meta (ImplicitPiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  pure (Success omega [ElemElaboration ctx dom dom' UniverseTy, ElemElaboration (ctx :< (x, El $ OmegaVarElim dom' Id)) cod cod' UniverseTy])
elabElemNuAtUniverse ops sig omega ctx (SigmaTy r x dom cod) meta = St.do
  (omega, dom') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  (omega, cod') <- liftUnifyM $ newElemMeta omega (ctx :< (x, El $ OmegaVarElim dom' Id)) UniverseTy SolveByElaboration
  let omega = Elem.instantiateByElaboration omega meta (SigmaTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  pure (Success omega [ElemElaboration ctx dom dom' UniverseTy, ElemElaboration (ctx :< (x, El $ OmegaVarElim dom' Id)) cod cod' UniverseTy])
elabElemNuAtUniverse ops sig omega ctx (FunTy r dom cod) meta = St.do
  (omega, dom') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  (omega, cod') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  let omega = Elem.instantiateByElaboration omega meta (PiTy "_" (OmegaVarElim dom' Id) (OmegaVarElim cod' Wk))
  pure (Success omega [ElemElaboration ctx dom dom' UniverseTy, ElemElaboration ctx cod cod' UniverseTy])
elabElemNuAtUniverse ops sig omega ctx (ProdTy r dom cod) meta = St.do
  (omega, dom') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  (omega, cod') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  let omega = Elem.instantiateByElaboration omega meta (SigmaTy "_" (OmegaVarElim dom' Id) ((OmegaVarElim cod' Wk)))
  pure (Success omega [ElemElaboration ctx dom dom' UniverseTy, ElemElaboration ctx cod cod' UniverseTy])
elabElemNuAtUniverse ops sig omega ctx (TyEqTy r a b) meta = St.do
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  let omega = Elem.instantiateByElaboration omega meta (TyEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id))
  pure (Success omega [ ElemElaboration ctx a a' UniverseTy,
                          ElemElaboration ctx b b' UniverseTy
                        ]
         )
elabElemNuAtUniverse ops sig omega ctx (ElEqTy r a b t) meta = St.do
  (omega, t') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx (El $ OmegaVarElim t' Id) SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (El $ OmegaVarElim t' Id) SolveByElaboration
  let omega = Elem.instantiateByElaboration omega meta (ElEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) (OmegaVarElim t' Id))
  pure (Success omega [ElemElaboration ctx t t' UniverseTy,
                         ElemElaboration ctx a a' (El $ OmegaVarElim t' Id),
                         ElemElaboration ctx b b' (El $ OmegaVarElim t' Id)
                        ]
         )
elabElemNuAtUniverse ops sig omega ctx (App r (NatTy x) []) meta = St.do
  let omega = Elem.instantiateByElaboration omega meta NatTy
  pure (Success omega [])
elabElemNuAtUniverse ops sig omega ctx (App r (ZeroTy x) []) meta = St.do
  let omega = Elem.instantiateByElaboration omega meta ZeroTy
  pure (Success omega [])
elabElemNuAtUniverse ops sig omega ctx (App r (OneTy x) []) meta = St.do
  let omega = Elem.instantiateByElaboration omega meta OneTy
  pure (Success omega [])
elabElemNuAtUniverse ops sig omega ctx tm meta =
  elabElemNuOtherwise ops sig omega ctx tm meta UniverseTy

public export
elabElemNuAtPi : Params
              => SnocList Operator
              -> Signature
              -> Omega
              -> Context
              -> SurfaceTerm
              -> OmegaName
              -> VarName
              -> Typ
              -> Typ
              -> ElabM Elaboration.Result
elabElemNuAtPi ops sig omega ctx (PiVal r x f) meta y dom cod = St.do
  (omega, f') <- liftUnifyM $ newElemMeta omega (ctx :< (x, dom)) cod SolveByElaboration
  let omega = Elem.instantiateByElaboration omega meta (PiVal x dom cod (OmegaVarElim f' Id))
  pure (Success omega [ElemElaboration (ctx :< (x, dom)) f f' cod])
elabElemNuAtPi ops sig omega ctx tm meta y dom cod = St.do
  elabElemNuOtherwise ops sig omega ctx tm meta (PiTy y dom cod)

public export
elabElemNuAtSigma : Params
                 => SnocList Operator
                 -> Signature
                 -> Omega
                 -> Context
                 -> SurfaceTerm
                 -> OmegaName
                 -> VarName
                 -> Typ
                 -> Typ
                 -> ElabM Elaboration.Result
elabElemNuAtSigma ops sig omega ctx (SigmaVal r a b) meta x dom cod = St.do
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx dom SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (ContextSubstElim cod (Ext Id (OmegaVarElim a' Id))) SolveByElaboration
  let omega = Elem.instantiateByElaboration omega meta (SigmaVal x dom cod (OmegaVarElim a' Id) (OmegaVarElim b' Id))
  pure (Success omega [ElemElaboration ctx a a' dom, ElemElaboration ctx b b' (ContextSubstElim cod (Ext Id (OmegaVarElim a' Id)))])
elabElemNuAtSigma ops sig omega ctx tm meta x dom cod = St.do
  elabElemNuOtherwise ops sig omega ctx tm meta (SigmaTy x dom cod)

public export
elabElemNuAtImplicitPi : Params
                      => SnocList Operator
                      -> Signature
                      -> Omega
                      -> Context
                      -> SurfaceTerm
                      -> OmegaName
                      -> VarName
                      -> Typ
                      -> Typ
                      -> ElabM Elaboration.Result
elabElemNuAtImplicitPi ops sig omega ctx (ImplicitPiVal r x f) meta y dom cod = St.do
  (omega, f') <- liftUnifyM $ newElemMeta omega (ctx :< (x, dom)) cod SolveByElaboration
  let omega = Elem.instantiateByElaboration omega meta (ImplicitPiVal x dom cod (OmegaVarElim f' Id))
  pure (Success omega [ElemElaboration (ctx :< (x, dom)) f f' cod])
elabElemNuAtImplicitPi ops sig omega ctx tm meta y dom cod = St.do
  elabElemNuOtherwise ops sig omega ctx tm meta (ImplicitPiTy y dom cod)

public export
elabElemNuAtNat : Params
               => SnocList Operator
               -> Signature
               -> Omega
               -> Context
               -> SurfaceTerm
               -> OmegaName
               -> ElabM Elaboration.Result
elabElemNuAtNat ops sig omega ctx (App r (NatVal0 x) []) meta = St.do
  let omega = Elem.instantiateByElaboration omega meta NatVal0
  pure (Success omega [])
elabElemNuAtNat ops sig omega ctx (App r (NatVal1 _) [(_, Arg ([], t))]) meta = St.do
  (omega, t') <- liftUnifyM $ newElemMeta omega ctx NatTy SolveByElaboration
  let omega = Elem.instantiateByElaboration omega meta (NatVal1 (OmegaVarElim t' Id))
  pure (Success omega [ElemElaboration ctx t t' NatTy])
elabElemNuAtNat ops sig omega ctx tm meta = St.do
  elabElemNuOtherwise ops sig omega ctx tm meta NatTy

public export
elabElemNuAtOne : Params
               => SnocList Operator
               -> Signature
               -> Omega
               -> Context
               -> SurfaceTerm
               -> OmegaName
               -> ElabM Elaboration.Result
elabElemNuAtOne ops sig omega ctx (App r (OneVal x) []) meta = St.do
  let omega = Elem.instantiateByElaboration omega meta OneVal
  pure (Success omega [])
elabElemNuAtOne ops sig omega ctx tm meta = St.do
  elabElemNuOtherwise ops sig omega ctx tm meta OneTy

public export
elabElemNuAtTyEq : Params
                => SnocList Operator
                -> Signature
                -> Omega
                -> Context
                -> SurfaceTerm
                -> OmegaName
                -> Typ
                -> Typ
                -> ElabM Elaboration.Result
elabElemNuAtTyEq ops sig omega ctx (App r (EqVal x) []) meta a b = St.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx a b)
  let omega = Elem.instantiateByElaboration omega meta (TyEqVal a)
  pure (Success omega [])
elabElemNuAtTyEq ops sig omega ctx tm meta a b = St.do
  elabElemNuOtherwise ops sig omega ctx tm meta (TyEqTy a b)

public export
elabElemNuAtElEq : Params
                => SnocList Operator
                -> Signature
                -> Omega
                -> Context
                -> SurfaceTerm
                -> OmegaName
                -> Elem
                -> Elem
                -> Typ
                -> ElabM Elaboration.Result
elabElemNuAtElEq ops sig omega ctx (App r (EqVal x) []) meta a b t = St.do
  omega <- liftUnifyM $ addConstraint omega (ElemConstraint ctx a b t)
  let omega = Elem.instantiateByElaboration omega meta (ElEqVal t a)
  pure (Success omega [])
elabElemNuAtElEq ops sig omega ctx tm meta a b t = St.do
  elabElemNuOtherwise ops sig omega ctx tm meta (ElEqTy a b t)


public export
elabElemNu : Params
          => SnocList Operator
          -> Signature
          -> Omega
          -> Context
          -> SurfaceTerm
          -> OmegaName
          -> CoreTyp
          -> ElabM Elaboration.Result
elabElemNu ops sig omega gamma tm meta UniverseTy =
  elabElemNuAtUniverse ops sig omega gamma tm meta
elabElemNu ops sig omega gamma tm meta (PiTy x dom cod) =
  elabElemNuAtPi ops sig omega gamma tm meta x dom cod
elabElemNu ops sig omega gamma tm meta (ImplicitPiTy x dom cod) =
  elabElemNuAtImplicitPi ops sig omega gamma tm meta x dom cod
elabElemNu ops sig omega gamma tm meta (SigmaTy x dom cod) =
  elabElemNuAtSigma ops sig omega gamma tm meta x dom cod
elabElemNu ops sig omega gamma tm meta NatTy =
  elabElemNuAtNat ops sig omega gamma tm meta
elabElemNu ops sig omega gamma tm meta OneTy =
  elabElemNuAtOne ops sig omega gamma tm meta
elabElemNu ops sig omega gamma tm meta (TyEqTy a b) =
  elabElemNuAtTyEq ops sig omega gamma tm meta a b
elabElemNu ops sig omega gamma tm meta (ElEqTy a b t) =
  elabElemNuAtElEq ops sig omega gamma tm meta a b t
elabElemNu ops sig omega gamma tm meta ty =
  elabElemNuOtherwise ops sig omega gamma tm meta ty

Nova.Surface.Elaboration.Interface.elabElem ops sig omega ctx tm p ty = St.do
  elabElemNu ops sig omega ctx tm p !(St.liftId $ openEval sig omega ty)

||| Σ Ω Γ ⊦ (t : T) ⟦ē⟧ ⇝ t' : A
||| Where T is head-neutral w.r.t. open evaluation.
public export
elabElemElimNu : Params
              => SnocList Operator
              -> Signature
              -> Omega
              -> Context
              -> CoreElem
              -> CoreTyp
              -> OpFreeElim
              -> OmegaName
              -> CoreTyp
              -> ElabM Elaboration.Result
elabElemElimNu ops sig omega ctx head (ImplicitPiTy x dom cod) ((_, ImplicitArg e) :: es) meta ty = St.do
  (omega, e') <- liftUnifyM $ newElemMeta omega ctx dom SolveByElaboration
  pure (Success omega [ElemElaboration ctx e e' dom,
                         ElemElimElaboration ctx (ImplicitPiElim head x dom cod (OmegaVarElim e' Id)) (ContextSubstElim cod (Ext Id (OmegaVarElim e' Id))) es meta ty])
elabElemElimNu ops sig omega ctx head (ImplicitPiTy x dom cod) es meta ty = St.do
  (omega, e') <- liftUnifyM $ newElemMeta omega ctx dom SolveByUnification
  pure (Success omega [ElemElimElaboration ctx (ImplicitPiElim head x dom cod (OmegaVarElim e' Id)) (ContextSubstElim cod (Ext Id (OmegaVarElim e' Id))) es meta ty])
elabElemElimNu ops sig omega ctx head headTy [] meta ty = St.do
  -- We have to make sure that the head is rigid (so that it can't become {_ : _} → _ later)
  case !(St.liftId (isRigid sig omega headTy)) of
    True => St.do
      omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx headTy ty)
      let omega = instantiateByElaboration omega meta head
      pure (Success omega [])
    False => St.do
      pure (Stuck "Head type is not rigid; headTy: \{renderDocNoAnn !(St.liftId $ prettyTypDefault sig omega (map fst ctx) headTy 0)}; expectedTy: \{renderDocNoAnn !(St.liftId $ prettyTypDefault sig omega (map fst ctx) ty 0)}")
elabElemElimNu ops sig omega ctx head (PiTy x dom cod) ((_, Arg ([], e)) :: es) meta ty = St.do
  (omega, e') <- liftUnifyM $ newElemMeta omega ctx dom SolveByElaboration
  pure (Success omega [ElemElaboration ctx e e' dom,
                         ElemElimElaboration ctx (PiElim head x dom cod (OmegaVarElim e' Id)) (ContextSubstElim cod (Ext Id (OmegaVarElim e' Id))) es meta ty])
elabElemElimNu ops sig omega ctx head (SigmaTy x dom cod) ((_, Pi1) :: es) meta ty = St.do
  pure (Success omega [ElemElimElaboration ctx (SigmaElim1 head x dom cod) dom es meta ty])
elabElemElimNu ops sig omega ctx head (SigmaTy x dom cod) ((_, Pi2) :: es) meta ty = St.do
  pure (Success omega [ElemElimElaboration ctx (SigmaElim2 head x dom cod) (ContextSubstElim cod (Ext Id (SigmaElim1 head x dom cod))) es meta ty])
{- elabElemElimNu sig omega ctx head headTy args@(Arg ([], e) :: es) meta ty = St.do
  (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, cod) <- liftUnifyM $ newTypeMeta omega (Ext ctx "_" (OmegaVarElim dom Id)) SolveByUnification
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx headTy (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)))
  pure (Success omega [ElemElimElaboration ctx head (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)) args meta ty]) -}
elabElemElimNu ops sig omega ctx head headTy elim meta ty =
  St.pure (Stuck "Waiting on head")

Nova.Surface.Elaboration.Interface.elabElemElim ops sig omega ctx head headTy es p ty = St.do
  elabElemElimNu ops sig omega ctx head !(St.liftId $ openEval sig omega headTy) es p !(St.liftId $ openEval sig omega ty)
