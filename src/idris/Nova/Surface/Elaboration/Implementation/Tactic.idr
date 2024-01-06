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
import Nova.Surface.Elaboration.Implementation.Tactic.NormaliseCommutativeMonoid
import Nova.Surface.Elaboration.Implementation.Tactic.TermLens
import Nova.Surface.Elaboration.Pretty

namespace Elem
  public export
  applyRewrite : Params
              => Signature
              -> Omega
              -> Context
              -> Elem
              -> OpFreeTerm
              -> SurfaceTerm
              -> Bool
              -> ElabM (Either (Range, Doc Ann) (Omega, Elem))
  applyRewrite sig omega gamma t p prf direct = MEither.do
    MkLens r gamma (Right (focused, setFocused)) <- Elab.liftM $ Elem.lens sig omega gamma t p
      | _ => error (range prf, "rewrite is not supported on types yet")
    case direct of
      True => MEither.do
        -- Γ ⊦ p : e₀ ≡ e ∈ A
        -- ⟦Γ | e | ☐ | p, True⟧ = e₀
        (omega, ty') <- liftUnifyM' $ newTypeMeta omega gamma SolveByUnification
        (omega, e0') <- liftUnifyM' $ newElemMeta omega gamma (OmegaVarElim ty' Id) SolveByUnification
        (omega, prf') <- liftUnifyM' $ newElemMeta omega gamma (ElEqTy (OmegaVarElim e0' Id) focused (OmegaVarElim ty' Id)) SolveByElaboration
        case !(mapResult Right (Interface.solve sig omega [ElemElaboration gamma prf prf' (ElEqTy (OmegaVarElim e0' Id) focused (OmegaVarElim ty' Id))])) of
          Success omega => MEither.do
            return (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega [] cons =>
            return (omega, OmegaVarElim e0' Id)
          Stuck omega elabs cons => MEither.do
            doc <- ElabEither.liftM $ pretty sig (Stuck omega elabs cons)
            error (r, doc)
          Error omega (Left err) => MEither.do
            let err = ElaborationError omega err
            error (r, !(ElabEither.liftM $ pretty sig err))
          Error omega (Right err) => MEither.do
            let err = UnificationError omega err
            error (r, !(ElabEither.liftM $ pretty sig err))
      False => MEither.do
        -- Γ ⊦ p : e ≡ e₀ ∈ A
        -- ⟦Γ | e | ☐ | p, False⟧ = e₀
        (omega, ty') <- liftUnifyM' $ newTypeMeta omega gamma SolveByUnification
        (omega, e0') <- liftUnifyM' $ newElemMeta omega gamma (OmegaVarElim ty' Id) SolveByUnification
        (omega, prf') <- liftUnifyM' $ newElemMeta omega gamma (ElEqTy focused (OmegaVarElim e0' Id) (OmegaVarElim ty' Id)) SolveByElaboration
        case !(mapResult Right (Interface.solve sig omega [ElemElaboration gamma prf prf' (ElEqTy focused (OmegaVarElim e0' Id) (OmegaVarElim ty' Id))])) of
          Success omega => MEither.do
            return (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega [] cons =>
            return (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega elabs cons => MEither.do
            doc <- ElabEither.liftM $ pretty sig (Stuck omega elabs cons)
            error (r, doc)
          Error omega (Left err) => MEither.do
            let err = ElaborationError omega err
            error (r, !(ElabEither.liftM $ pretty sig err))
          Error omega (Right err) => MEither.do
            let err = UnificationError omega err
            error (r, !(ElabEither.liftM $ pretty sig err))

namespace Typ
  public export
  applyRewrite : Params
              => Signature
              -> Omega
              -> Context
              -> Typ
              -> OpFreeTerm
              -> SurfaceTerm
              -> Bool
              -> ElabM (Either (Range, Doc Ann) (Omega, Typ))
  applyRewrite sig omega gamma t p prf direct = MEither.do
    MkLens r gamma (Right (focused, setFocused)) <- Elab.liftM $ Typ.lens sig omega gamma t p
      | _ => error (range prf, "rewrite is not supported on types yet")
    case direct of
      True => MEither.do
        -- Γ ⊦ p : e₀ ≡ e ∈ A
        -- ⟦Γ | e | ☐ | p, True⟧ = e₀
        (omega, ty') <- liftUnifyM' $ newTypeMeta omega gamma SolveByUnification
        (omega, e0') <- liftUnifyM' $ newElemMeta omega gamma (OmegaVarElim ty' Id) SolveByUnification
        (omega, prf') <- liftUnifyM' $ newElemMeta omega gamma (ElEqTy (OmegaVarElim e0' Id) focused (OmegaVarElim ty' Id)) SolveByElaboration
        case !(mapResult Right (Interface.solve sig omega [ElemElaboration gamma prf prf' (ElEqTy (OmegaVarElim e0' Id) focused (OmegaVarElim ty' Id))])) of
          Success omega => MEither.do
            return (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega [] cons =>
            return (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega elabs cons => MEither.do
            -- write "rewrite failed at ☐, got stuck elaborations:" <&> Right
            doc <- ElabEither.liftM $ pretty sig (Stuck omega elabs cons)
            -- write (renderDocTerm doc) <&> Right
            error (r, doc)
          Error omega (Left err) => MEither.do
            let err = ElaborationError omega err
            -- write "rewrite failed at ☐:" <&> Right
            -- write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right
            error (r, !(ElabEither.liftM $ pretty sig err))
          Error omega (Right err) => MEither.do
            let err = UnificationError omega err
            -- write "rewrite failed at ☐:" <&> Right
            -- write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right
            error (r, !(ElabEither.liftM $ pretty sig err))
      False => MEither.do
        -- Γ ⊦ p : e ≡ e₀ ∈ A
        -- ⟦Γ | e | ☐ | p, False⟧ = e₀
        (omega, ty') <- liftUnifyM' $ newTypeMeta omega gamma SolveByUnification
        (omega, e0') <- liftUnifyM' $ newElemMeta omega gamma (OmegaVarElim ty' Id) SolveByUnification
        (omega, prf') <- liftUnifyM' $ newElemMeta omega gamma (ElEqTy focused (OmegaVarElim e0' Id) (OmegaVarElim ty' Id)) SolveByElaboration
        case !(mapResult Right (Interface.solve sig omega [ElemElaboration gamma prf prf' (ElEqTy focused (OmegaVarElim e0' Id) (OmegaVarElim ty' Id))])) of
          Success omega => MEither.do
            return (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega [] cons =>
            return (omega, setFocused (OmegaVarElim e0' Id))
          Stuck omega elabs cons => MEither.do
            -- write "rewrite⁻¹ failed at ☐, got stuck elaborations:" <&> Right
            doc <- ElabEither.liftM $ pretty sig (Stuck omega elabs cons)
            -- write (renderDocTerm doc) <&> Right
            error (r, doc)
          Error omega (Left err) => MEither.do
            let err = ElaborationError omega err
            {- write "rewrite⁻¹ failed at ☐:" <&> Right
            write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right -}
            error (r, !(ElabEither.liftM $ pretty sig err))
          Error omega (Right err) => MEither.do
            let err = UnificationError omega err
            {- write "rewrite⁻¹ failed at ☐:" <&> Right
            write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right -}
            error (r, !(ElabEither.liftM $ pretty sig err))

Nova.Surface.Elaboration.Interface.elabTactic sig omega (Id r) target = M.do
  write (renderDocTerm !(Elab.liftM $ prettySignature sig omega target))
  return (Right (omega, target, id))
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Trivial r) [< (x, ElemEntry ctx ty)] = M.do
  case !(Elab.liftM $ applyTrivial sig omega ty) of
    Just done => return (Right (omega, [<], \_ => [< ElemEntryInstance done]))
    Nothing => return (Left (r, "Can't apply 'trivial'"))
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Trivial r) _ = MEither.do
  error (r, "Wrong signature for tactic: 'trivial'")
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Composition r (alpha ::: [])) target = M.do
  Nova.Surface.Elaboration.Interface.elabTactic sig omega alpha target
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Composition r (alpha ::: beta :: gammas)) target = MEither.do
  (omega, alphaSource, alphaInterp) <- Nova.Surface.Elaboration.Interface.elabTactic sig omega alpha target
  (omega, source, restInterp) <- Nova.Surface.Elaboration.Interface.elabTactic sig omega (Composition r (beta ::: gammas)) alphaSource
  return (omega, source, restInterp . alphaInterp)
-- ⟦unfold ρ⟧ : ε (Γ ⊦ B) ⇒ ε (Γ ⊦ A)
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Unfold r path) [< (x, ElemEntry ctx ty)] = M.do
 Right ty' <- Elab.liftM $ applyUnfold sig omega (map fst ctx) ty path
   | Left r => --FIX: use the range
               return (Left (r, pretty "Can't apply 'unfold', ρ: \{show path}"))
 return (Right (omega, [< (x, ElemEntry ctx ty')], id))
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Unfold r path) _ = MEither.do
  error (r, "Target context is empty or its last entry is a let")
Nova.Surface.Elaboration.Interface.elabTactic sig omega (RewriteInv r path prf) [< (x, ElemEntry ctx ty)] = MEither.do
  (omega, ty0) <- applyRewrite sig omega ctx ty path prf False
  return (omega, [< (x, ElemEntry ctx ty0)], id)
Nova.Surface.Elaboration.Interface.elabTactic sig omega (RewriteInv r path prf) target = MEither.do
  error (r, "Wrong context for rewrite⁻¹")
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Rewrite r path prf) [< (x, ElemEntry ctx ty)] = MEither.do
  (omega, ty0) <- applyRewrite sig omega ctx ty path prf True
  return (omega, [< (x, ElemEntry ctx ty0)], id)
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Rewrite r path prf) target = MEither.do
  error (r, "Wrong context for rewrite")
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Exact r tm) [< (x, ElemEntry ctx ty)] = M.do
  (omega, m') <- liftUnifyM $ newElemMeta omega ctx ty SolveByElaboration
  case !(Interface.solve sig omega [ElemElaboration ctx tm m' ty]) of
    Success omega =>
       return (Right (omega, [<], \_ => [< ElemEntryInstance (OmegaVarElim m' Id)]))
    Stuck omega [] cons =>
       return (Right (omega, [<], \_ => [< ElemEntryInstance (OmegaVarElim m' Id)]))
    Stuck omega elabs cons => M.do
      let err = Stuck omega elabs cons
      return (Left (r, "Stuck elaborating the exact term:" <+> hardline <+> !(liftM $ pretty sig err)))
    Error omega (Left err) => MEither.do
      let err = ElaborationError omega err
      error (r, "Error elaborating the exact term" <+> hardline <+> !(ElabEither.liftM $ pretty sig err))
    Error omega (Right err) => MEither.do
      let err = UnificationError omega err
      error (r, "Error elaborating the exact term" <+> hardline <+> !(ElabEither.liftM $ pretty sig err))
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Exact r tm) target = MEither.do
  error (r, "Wrong target context for exact tactic")
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Split r [<] alpha) target =
  Nova.Surface.Elaboration.Interface.elabTactic sig omega alpha target
-- THOUGHT: Pretty sure Split can be generalised such that the source context is arbitrary
-- ⟦α⟧ ⇝ α' : ε ⇒ Σ
-- ⟦β⟧ ⇝ β' : ε ⇒ (Γ(id, α' ·) ⊦ A(id, α' ·))
-- --------------------------
-- ⟦* α * β⟧ ⇝ \x => α' x, β' x : ε ⇒ Σ (Γ ⊦ A)
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Split r (betas :< beta) alpha) (sigma :< (x, ElemEntry ctx ty)) = MEither.do
  (omega, [<], interpA) <- Nova.Surface.Elaboration.Interface.elabTactic sig omega (Split r betas beta) sigma
    | _ => error (r, "Error elaborating Split: wrong source context of one of the arguments")
  (omega, [<], interpB) <- Nova.Surface.Elaboration.Interface.elabTactic sig omega alpha [< (x, ElemEntry (subst ctx (ext Id (cast (interpA [<])))) (SignatureSubstElim ty (ext Id (cast (interpA [<])))))]
    | _ => error (r, "Error elaborating Split: wrong source context of one of the arguments")
  return (omega, [<], \x => interpA x ++ interpB x)
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Split r (betas :< beta) alpha) target = MEither.do
  error (r, "Wrong target context for split tactic")
Nova.Surface.Elaboration.Interface.elabTactic sig omega (Let r x e) target = M.do
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
        False => return (Left (range e, "Stuck elaborating RHS of let; have some unsolved holes:" <+> hardline <+> !(Elab.liftM $ prettyOmega sig omega)))
    Stuck omega elabs cons => M.do
      let err = Stuck omega elabs cons
      return (Left (r, "Stuck elaborating RHS of let" <+> hardline <+> !(liftM $ pretty sig err)))
    Error omega (Left err) => MEither.do
      let err = ElaborationError omega err
      error (r, "Error elaborating the RHS of let" <+> hardline <+> !(ElabEither.liftM $ pretty sig err))
    Error omega (Right err) => MEither.do
      let err = UnificationError omega err
      error (r, "Error elaborating the RHS of let" <+> hardline <+> !(ElabEither.liftM $ pretty sig err))
Nova.Surface.Elaboration.Interface.elabTactic sig omega (NormaliseCommutativeMonoid r path monoidTm e) target = M.do
  elabNormaliseComm sig omega r path monoidTm e target
