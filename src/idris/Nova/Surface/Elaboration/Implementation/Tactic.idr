module Nova.Surface.Elaboration.Implementation.Tactic

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
import Nova.Surface.Elaboration.Implementation.Tactic.Trivial
import Nova.Surface.Elaboration.Implementation.Tactic.Unfold
import Nova.Surface.Elaboration.Implementation.Tactic.NormaliseCommutativeMonoid
import Nova.Surface.Elaboration.Implementation.Tactic.TermLens
import Nova.Surface.Elaboration.Pretty

namespace Elem
  public export
  applyRewrite : Params
              => SnocList Operator
              -> Signature
              -> Omega
              -> Context
              -> Elem
              -> OpFreeTerm
              -> SurfaceTerm
              -> Bool
              -> StEither (Range, Doc Ann) ElabSt (Omega, Elem)
  applyRewrite ops sig omega gamma t p prf direct = StEither.do
    MkLens r gamma (Right (focused, setFocused)) <- StEither.fromEither $ Elem.lens sig omega gamma t p
      | _ => throw (range prf, "rewrite is not supported on types yet")
    case direct of
      True => StEither.do
        -- Γ ⊦ p : e₀ ≡ e ∈ A
        -- ⟦Γ | e | ☐ | p, True⟧ = e₀
        (omega, ty') <- liftUnifyM' $ newTypeMeta omega gamma SolveByUnification
        (omega, e0') <- liftUnifyM' $ newElemMeta omega gamma (OmegaVarElim ty' Id) SolveByUnification
        (omega, prf') <- liftUnifyM' $ newElemMeta omega gamma (ElEqTy (OmegaVarElim e0' Id) focused (OmegaVarElim ty' Id)) SolveByElaboration
        case with StEither.(<$>) !(Right <$> Interface.solve ops sig omega [ElemElaboration gamma prf prf' (ElEqTy (OmegaVarElim e0' Id) focused (OmegaVarElim ty' Id))]) of
          Success omega => StEither.do
            pure (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega [] cons =>
            StEither.pure (omega, OmegaVarElim e0' Id)
          Stuck omega elabs cons => StEither.do
            doc <- StEither.liftId $ prettyDefault sig (Stuck omega elabs cons)
            throw (r, doc)
          Error omega (Left err) => StEither.do
            let err = ElaborationError omega err
            throw (r, !(StEither.liftId $ prettyDefault sig err))
          Error omega (Right err) => StEither.do
            let err = UnificationError omega err
            throw (r, !(StEither.liftId $ prettyDefault sig err))
      False => StEither.do
        -- Γ ⊦ p : e ≡ e₀ ∈ A
        -- ⟦Γ | e | ☐ | p, False⟧ = e₀
        (omega, ty') <- liftUnifyM' $ newTypeMeta omega gamma SolveByUnification
        (omega, e0') <- liftUnifyM' $ newElemMeta omega gamma (OmegaVarElim ty' Id) SolveByUnification
        (omega, prf') <- liftUnifyM' $ newElemMeta omega gamma (ElEqTy focused (OmegaVarElim e0' Id) (OmegaVarElim ty' Id)) SolveByElaboration
        case with StEither.(<$>) !(Right <$> Interface.solve ops sig omega [ElemElaboration gamma prf prf' (ElEqTy focused (OmegaVarElim e0' Id) (OmegaVarElim ty' Id))]) of
          Success omega => StEither.do
            pure (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega [] cons =>
            pure (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega elabs cons => StEither.do
            doc <- StEither.liftId $ prettyDefault sig (Stuck omega elabs cons)
            throw (r, doc)
          Error omega (Left err) => StEither.do
            let err = ElaborationError omega err
            throw (r, !(StEither.liftId $ prettyDefault sig err))
          Error omega (Right err) => StEither.do
            let err = UnificationError omega err
            throw (r, !(StEither.liftId $ prettyDefault sig err))

namespace Typ
  public export
  applyRewrite : Params
              => SnocList Operator
              -> Signature
              -> Omega
              -> Context
              -> Typ
              -> OpFreeTerm
              -> SurfaceTerm
              -> Bool
              -> StEither (Range, Doc Ann) ElabSt (Omega, Typ)
  applyRewrite ops sig omega gamma t p prf direct = StEither.do
    MkLens r gamma (Right (focused, setFocused)) <- StEither.fromEither $ Typ.lens sig omega gamma t p
      | _ => throw (range prf, "rewrite is not supported on types yet")
    case direct of
      True => StEither.do
        -- Γ ⊦ p : e₀ ≡ e ∈ A
        -- ⟦Γ | e | ☐ | p, True⟧ = e₀
        (omega, ty') <- liftUnifyM' $ newTypeMeta omega gamma SolveByUnification
        (omega, e0') <- liftUnifyM' $ newElemMeta omega gamma (OmegaVarElim ty' Id) SolveByUnification
        (omega, prf') <- liftUnifyM' $ newElemMeta omega gamma (ElEqTy (OmegaVarElim e0' Id) focused (OmegaVarElim ty' Id)) SolveByElaboration
        case with StEither.(<$>) !(Right <$> Interface.solve ops sig omega [ElemElaboration gamma prf prf' (ElEqTy (OmegaVarElim e0' Id) focused (OmegaVarElim ty' Id))]) of
          Success omega => StEither.do
            pure (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega [] cons =>
            pure (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega elabs cons => StEither.do
            -- write "rewrite failed at ☐, got stuck elaborations:" <&> Right
            doc <- StEither.liftId $ prettyDefault sig (Stuck omega elabs cons)
            -- write (renderDocTerm doc) <&> Right
            throw (r, doc)
          Error omega (Left err) => StEither.do
            let err = ElaborationError omega err
            -- write "rewrite failed at ☐:" <&> Right
            -- write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right
            throw (r, !(StEither.liftId $ prettyDefault sig err))
          Error omega (Right err) => StEither.do
            let err = UnificationError omega err
            -- write "rewrite failed at ☐:" <&> Right
            -- write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right
            throw (r, !(StEither.liftId $ prettyDefault sig err))
      False => StEither.do
        -- Γ ⊦ p : e ≡ e₀ ∈ A
        -- ⟦Γ | e | ☐ | p, False⟧ = e₀
        (omega, ty') <- liftUnifyM' $ newTypeMeta omega gamma SolveByUnification
        (omega, e0') <- liftUnifyM' $ newElemMeta omega gamma (OmegaVarElim ty' Id) SolveByUnification
        (omega, prf') <- liftUnifyM' $ newElemMeta omega gamma (ElEqTy focused (OmegaVarElim e0' Id) (OmegaVarElim ty' Id)) SolveByElaboration
        case with StEither.(<$>) !(Right <$> Interface.solve ops sig omega [ElemElaboration gamma prf prf' (ElEqTy focused (OmegaVarElim e0' Id) (OmegaVarElim ty' Id))]) of
          Success omega => StEither.do
            pure (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega [] cons =>
            pure (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega elabs cons => StEither.do
            -- write "rewrite⁻¹ failed at ☐, got stuck elaborations:" <&> Right
            doc <- StEither.liftId $ prettyDefault sig (Stuck omega elabs cons)
            -- write (renderDocTerm doc) <&> Right
            throw (r, doc)
          Error omega (Left err) => StEither.do
            let err = ElaborationError omega err
            {- write "rewrite⁻¹ failed at ☐:" <&> Right
            write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right -}
            throw (r, !(StEither.liftId $ prettyDefault sig err))
          Error omega (Right err) => StEither.do
            let err = UnificationError omega err
            {- write "rewrite⁻¹ failed at ☐:" <&> Right
            write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right -}
            throw (r, !(StEither.liftId $ prettyDefault sig err))

Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Id r) target = StEither.do
  -- write (renderDocTerm !(StEither.liftId $ prettySignatureDefault sig omega target))
  pure (omega, target, id)
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Trivial r) [< (x, ElemEntry ctx ty)] = StEither.do
  case applyTrivial sig omega ty of
    Just done => StEither.pure (omega, [<], \_ => [< ElemEntryInstance done])
    Nothing => throw (r, "Can't apply 'trivial'")
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Trivial r) _ = StEither.do
  throw (r, "Wrong signature for tactic: 'trivial'")
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Composition r (alpha ::: [])) target = StEither.do
  Nova.Surface.Elaboration.Interface.elabTactic ops sig omega alpha target
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Composition r (alpha ::: beta :: gammas)) target = StEither.do
  (omega, alphaSource, alphaInterp) <- Nova.Surface.Elaboration.Interface.elabTactic ops sig omega alpha target
  (omega, source, restInterp) <- Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Composition r (beta ::: gammas)) alphaSource
  pure (omega, source, restInterp . alphaInterp)
-- ⟦unfold ρ⟧ : ε (Γ ⊦ B) ⇒ ε (Γ ⊦ A)
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Unfold r path) [< (x, ElemEntry ctx ty)] = StEither.do
 let Right ty' = applyUnfold sig omega (map fst ctx) ty path
   | Left r => --FIX: use the range
               throw (r, pretty "Can't apply 'unfold', ρ: \{show path}")
 pure (omega, [< (x, ElemEntry ctx ty')], id)
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Unfold r path) _ = StEither.do
  throw (r, "Target context is empty or its last entry is a let")
-- ⟦unfold ρ⟧ : ε (Γ' ⊦ A) ⇒ ε (Γ ⊦ A)
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (UnfoldCtx r path) [< (x, ElemEntry ctx ty)] = StEither.do
  let Right ctx' = Ctx.applyUnfold sig omega ctx path
    | Left r => --FIX: use the range
                throw (r, pretty "Can't apply 'unfold-ctx'")
  pure (omega, [< (x, ElemEntry ctx' ty)], id)
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (UnfoldCtx r path) _ = StEither.do
  throw (r, "Target context is empty or its last entry is a let")
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (RewriteInv r path prf) [< (x, ElemEntry ctx ty)] = StEither.do
  (omega, ty0) <- applyRewrite ops sig omega ctx ty path prf False
  pure (omega, [< (x, ElemEntry ctx ty0)], id)
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (RewriteInv r path prf) target = StEither.do
  throw (r, "Wrong context for rewrite⁻¹")
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Rewrite r path prf) [< (x, ElemEntry ctx ty)] = StEither.do
  (omega, ty0) <- applyRewrite ops sig omega ctx ty path prf True
  pure (omega, [< (x, ElemEntry ctx ty0)], id)
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Rewrite r path prf) target = StEither.do
  throw (r, "Wrong context for rewrite")
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Exact r tm) [< (x, ElemEntry ctx ty)] = StEither.do
  (omega, m') <- liftUnifyM' $ newElemMeta omega ctx ty SolveByElaboration
  case !(StEither.liftSt $ Interface.solve ops sig omega [ElemElaboration ctx tm m' ty]) of
    Success omega =>
       StEither.pure (omega, [<], \_ => [< ElemEntryInstance (OmegaVarElim m' Id)])
    Stuck omega [] cons =>
       StEither.pure (omega, [<], \_ => [< ElemEntryInstance (OmegaVarElim m' Id)])
    Stuck omega elabs cons => StEither.do
      let err = Stuck omega elabs cons
      throw (r, "Stuck elaborating the exact term:" <+> hardline <+> prettyDefault sig err)
    Error omega (Left err) => StEither.do
      let err = ElaborationError omega err
      throw (r, "Error elaborating the exact term" <+> hardline <+> prettyDefault sig err)
    Error omega (Right err) => StEither.do
      let err = UnificationError omega err
      throw (r, "Error elaborating the exact term" <+> hardline <+> (prettyDefault sig err))
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Exact r tm) target = StEither.do
  throw (r, "Wrong target context for exact tactic")
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Split r [<] alpha) target =
  Nova.Surface.Elaboration.Interface.elabTactic ops sig omega alpha target
-- THOUGHT: Pretty sure Split can be generalised such that the source context is arbitrary
-- ⟦α⟧ ⇝ α' : ε ⇒ Σ
-- ⟦β⟧ ⇝ β' : ε ⇒ (Γ(id, α' ·) ⊦ A(id, α' ·))
-- --------------------------
-- ⟦* α * β⟧ ⇝ \x => α' x, β' x : ε ⇒ Σ (Γ ⊦ A)
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Split r (betas :< beta) alpha) (sigma :< (x, ElemEntry ctx ty)) = StEither.do
  (omega, [<], interpA) <- Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Split r betas beta) sigma
    | _ => throw (r, "Error elaborating Split: wrong source context of one of the arguments")
  (omega, [<], interpB) <- Nova.Surface.Elaboration.Interface.elabTactic ops sig omega alpha [< (x, ElemEntry (subst ctx (ext Id (cast (interpA [<])))) (SignatureSubstElim ty (ext Id (cast (interpA [<])))))]
    | _ => throw (r, "Error elaborating Split: wrong source context of one of the arguments")
  pure (omega, [<], \x => interpA x ++ interpB x)
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Split r (betas :< beta) alpha) target = StEither.do
  throw (r, "Wrong target context for split tactic")
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Let r x e) target@[< (_, ElemEntry ctx _)] = StEither.do
  (omega, ty') <- liftUnifyM' $ newTypeMeta omega ctx SolveByUnification
  let ty = OmegaVarElim ty' Id
  (omega, e') <- liftUnifyM' $ newElemMeta omega ctx ty SolveByElaboration
  -- Σ (x ≔ t : A)
  let source = target :< (x, LetElemEntry ctx (OmegaVarElim e' Id) ty)
  let
    f : SignatureInst -> SignatureInst
    f [<] = assert_total $ idris_crash "Nova.Surface.Elaboration.Interface.elabTactic/let"
    f (ts :< t) = ts
  case !(StEither.liftSt $ Interface.solve ops sig omega [ElemElaboration ctx e e' ty]) of
    Success omega =>
      StEither.pure (omega, source, f)
                --FIX:
    Stuck omega [] [] =>
      case (containsNamedHolesOnly omega) of
        True =>
          StEither.pure (omega, source, f)
        False => throw (range e, "Stuck elaborating RHS of let; have some unsolved holes:" <+> hardline <+> prettyOmegaDefault sig omega)
    Stuck omega elabs cons => StEither.do
      let err = Stuck omega elabs cons
      throw (r, "Stuck elaborating RHS of let" <+> hardline <+> prettyDefault sig err)
    Error omega (Left err) => StEither.do
      let err = ElaborationError omega err
      throw (r, "Error elaborating the RHS of let" <+> hardline <+> prettyDefault sig err)
    Error omega (Right err) => StEither.do
      let err = UnificationError omega err
      throw (r, "Error elaborating the RHS of let" <+> hardline <+> prettyDefault sig err)
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (Let r x e) target = ?todoThrow
Nova.Surface.Elaboration.Interface.elabTactic ops sig omega (NormaliseCommutativeMonoid r path monoidTm e) target = StEither.do
  elabNormaliseComm ops sig omega r path monoidTm e target
