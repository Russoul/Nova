module Nova.Surface.Elaboration.Implementation.Typ

import Me.Russoul.Data.Location

import Nova.Control.Monad.Id
import Nova.Control.Monad.St

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

Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (PiTy r x dom cod) meta = St.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (PiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  pure (Success omega [TypeElaboration ctx dom dom', TypeElaboration (ctx :< (x, OmegaVarElim dom' Id)) cod cod'])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (ImplicitPiTy r x dom cod) meta = St.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (ImplicitPiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  pure (Success omega [TypeElaboration ctx dom dom', TypeElaboration (ctx :< (x, OmegaVarElim dom' Id)) cod cod'])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (SigmaTy r x dom cod) meta = St.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (SigmaTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  pure (Success omega [TypeElaboration ctx dom dom', TypeElaboration (ctx :< (x, OmegaVarElim dom' Id)) cod cod'])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (FunTy r dom cod) meta = St.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (PiTy "_" (OmegaVarElim dom' Id) (OmegaVarElim cod' Wk))
  pure (Success omega [TypeElaboration ctx dom dom', TypeElaboration ctx cod cod'])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (ProdTy r dom cod) meta = St.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (SigmaTy "_" (OmegaVarElim dom' Id) (OmegaVarElim cod' Wk))
  pure (Success omega [TypeElaboration ctx dom dom', TypeElaboration ctx cod cod'])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (TyEqTy r a b) meta = St.do
  (omega, a') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, b') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (TyEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id))
  pure (Success omega [ TypeElaboration ctx a a',
                          TypeElaboration ctx b b'
                        ]
         )
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (ElEqTy r a b t) meta = St.do
  (omega, t') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (ElEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) (OmegaVarElim t' Id))
  pure (Success omega [TypeElaboration ctx t t',
                         ElemElaboration ctx a a' (OmegaVarElim t' Id),
                         ElemElaboration ctx b b' (OmegaVarElim t' Id)
                        ]
         )
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (PiVal r x f) meta =
  St.pure (Error "_ ↦ _ is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (ImplicitPiVal r x f) meta =
  St.pure (Error "{_} ↦ _ is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (SigmaVal r a b) meta =
  St.pure (Error "(_, _) is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx tm@(App r (Var r0 x) es) meta = St.do
  case (lookupTypeSignature sig x, es) of
    (Just ([<], idx), []) => St.do
      addSemanticToken (r0, ElimAnn)
      let omega = Typ.instantiateByElaboration omega meta (SignatureVarElim idx Terminal)
      pure (Success omega [])
    (Just ([<], idx), _ :: _) => St.do
      pure (Error "Type variable \{x} applied to a spine")
    (Just (_ :< _, idx), _) =>
      pure (Error "Non-empty signature context not supported yet for name: \{x}")
    (Nothing, es) =>
      case (lookup x omega, es) of
        (Just (LetType [<] _), []) => St.do
          addSemanticToken (r0, ElimAnn)
          let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim x Terminal)
          pure (Success omega [])
        (Just (LetType (_ :< _) _), _) => St.do
          pure (Error "Non-empty signature context not supported yet for name: \{x}")
        (Just (LetType [<] _), _ :: _) => St.do
          pure (Error "Type variable \{x} applied to a spine")
        _ => St.do
         (omega, t') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
         let omega = Typ.instantiateByElaboration omega meta (El (OmegaVarElim t' Id))
         pure (Success omega [ElemElaboration ctx tm t' UniverseTy])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (OneVal x) _) meta = St.do
  pure (Error "() is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (NatVal0 x) _) meta = St.do
  pure (Error "Z is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (NatVal1 _) _) meta = St.do
  pure (Error "S is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx tm@(App r (NatElim _) _) meta = St.do
  (omega, t') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (El (OmegaVarElim t' Id))
  pure (Success omega [ElemElaboration ctx tm t' UniverseTy])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx tm@(App r (ZeroElim _) _) meta = St.do
  (omega, t') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (El (OmegaVarElim t' Id))
  pure (Success omega [ElemElaboration ctx tm t' UniverseTy])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App _ (EqElim _) _) meta = St.do
  pure (Error "J is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (EqVal x) _) meta = St.do
  pure (Error "Refl is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (NatTy x) []) meta = St.do
  let omega = Typ.instantiateByElaboration omega meta NatTy
  pure (Success omega [])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (NatTy x) _) meta =
  St.pure (Error "ℕ applied to a wrong number of arguments")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (ZeroTy x) []) meta = St.do
  let omega = Typ.instantiateByElaboration omega meta ZeroTy
  St.pure (Success omega [])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (ZeroTy x) _) meta =
  St.pure (Error "𝟘 applied to a wrong number of arguments")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (OneTy x) []) meta = St.do
  let omega = Typ.instantiateByElaboration omega meta OneTy
  pure (Success omega [])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (OneTy x) _) meta =
  St.pure (Error "𝟙 applied to a wrong number of arguments")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (UniverseTy x) []) meta = St.do
  let omega = Typ.instantiateByElaboration omega meta UniverseTy
  St.pure (Success omega [])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (UniverseTy x) _) meta =
  St.pure (Error "𝕌 applied to a wrong number of arguments")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (UnnamedHole r0 Nothing) []) meta = St.do
  (omega, n) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim n Id)
  pure (Success omega [])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (UnnamedHole r0 (Just vars)) []) meta = St.do
  let Just regctxPrefix = pickPrefix (cast ctx) vars
    | Nothing => St.pure (Error "Invalid context prefix")
  let ctxPrefix = cast regctxPrefix
  (omega, n) <- liftUnifyM $ newTypeMeta omega ctxPrefix SolveByUnification
  let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim n (WkN (length ctx `minus` length regctxPrefix)))
  pure (Success omega [])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (UnnamedHole x vars) _) meta =
  St.pure (Error "? applied to arguments not supported")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (Hole r0 n Nothing) es) meta =
  case (lookup n omega) of
    Just _ => pure (Error "Hole already exists: \{n}")
    Nothing => St.do
      omega <- liftUnifyM $ newTypeMeta omega ctx n NoSolve
      let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim n Id)
      St.Maybe.for_ (the Params %search).absFilePath (\path => addNamedHole path r0 n)
      pure (Success omega [])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (Hole r0 n (Just vars)) es) meta =
  case (lookup n omega) of
    Just _ => pure (Error "Hole already exists: \{n}")
    Nothing => St.do
      let Just regctxPrefix = pickPrefix (cast ctx) vars
        | Nothing => St.pure (Error "Invalid context prefix")
      let ctxPrefix = cast regctxPrefix
      omega <- liftUnifyM $ newTypeMeta omega ctxPrefix n SolveByUnification
      let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim n (WkN (length ctx `minus` length regctxPrefix)))
      pure (Success omega [])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (Unfold r0 x) _) meta = St.do
  pure (Error "! is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx tm@(App r (PiBeta r0) _) meta = St.do
  pure (Error "Π-β is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx tm@(App r (SigmaBeta1 r0) _) meta = St.do
  pure (Error "Σ-β₁ is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx tm@(App r (SigmaBeta2 r0) _) meta = St.do
  pure (Error "Σ-β₂ is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (PiEta r0) _) meta = St.do
  pure (Error "Π-η is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (SigmaEta r0) _) meta = St.do
  pure (Error "Σ-η is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (NatBetaZ r0) _) meta = St.do
  pure (Error "ℕ-β-Z is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (NatBetaS r0) _) meta = St.do
  pure (Error "ℕ-β-S is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (PiEq r0) _) meta = St.do
  pure (Error "Π⁼ is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (SigmaEq r0) _) meta = St.do
  pure (Error "Σ⁼ is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (OneEq r0) _) meta = St.do
  pure (Error "𝟙⁼ is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (Tm _ tm) []) meta = St.do
  pure (Success omega [TypeElaboration ctx tm meta])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (Tm _ tm) es) meta = St.do
  pure (Error "_ _ is not a type")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (Tac r alpha) meta = St.do
  pure (Error "tac is not supported in a type yet")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (Underscore r0) _) meta =
  St.pure (Error "_ is not a valid term")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (Box r0) _) meta =
  St.pure (Error "☐ is not a valid term")
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (El r0) [(_, Arg ([], el))]) meta = St.do
  -- ⟦e⟧ : 𝕌
  -- -------------------
  -- ⟦El e⟧ ⇝ El e' type
  (omega, el') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (El (OmegaVarElim el' Id))
  pure (Success omega [ElemElaboration ctx el el' UniverseTy])
Nova.Surface.Elaboration.Interface.elabType ops sig omega ctx (App r (El r0) _) meta = St.do
  St.pure (Error "El applied to a wrong number of arguments")
