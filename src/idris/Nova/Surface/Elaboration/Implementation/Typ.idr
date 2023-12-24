module Nova.Surface.Elaboration.Implementation.Typ

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

Nova.Surface.Elaboration.Interface.elabType sig omega ctx (PiTy r x dom cod) meta = M.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (PiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  return (Success omega [TypeElaboration ctx dom dom', TypeElaboration (ctx :< (x, OmegaVarElim dom' Id)) cod cod'])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (ImplicitPiTy r x dom cod) meta = M.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (ImplicitPiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  return (Success omega [TypeElaboration ctx dom dom', TypeElaboration (ctx :< (x, OmegaVarElim dom' Id)) cod cod'])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (SigmaTy r x dom cod) meta = M.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (SigmaTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  return (Success omega [TypeElaboration ctx dom dom', TypeElaboration (ctx :< (x, OmegaVarElim dom' Id)) cod cod'])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (FunTy r dom cod) meta = M.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (PiTy "_" (OmegaVarElim dom' Id) (OmegaVarElim cod' Wk))
  return (Success omega [TypeElaboration ctx dom dom', TypeElaboration ctx cod cod'])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (ProdTy r dom cod) meta = M.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (SigmaTy "_" (OmegaVarElim dom' Id) (OmegaVarElim cod' Wk))
  return (Success omega [TypeElaboration ctx dom dom', TypeElaboration ctx cod cod'])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (TyEqTy r a b) meta = M.do
  (omega, a') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, b') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (TyEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id))
  return (Success omega [ TypeElaboration ctx a a',
                          TypeElaboration ctx b b'
                        ]
         )
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (ElEqTy r a b t) meta = M.do
  (omega, t') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (ElEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) (OmegaVarElim t' Id))
  return (Success omega [TypeElaboration ctx t t',
                         ElemElaboration ctx a a' (OmegaVarElim t' Id),
                         ElemElaboration ctx b b' (OmegaVarElim t' Id)
                        ]
         )
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (PiVal r x f) meta =
  return (Error "_ ↦ _ is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (ImplicitPiVal r x f) meta =
  return (Error "{_} ↦ _ is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (SigmaVal r a b) meta =
  return (Error "(_, _) is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx tm@(App r (Var r0 x) es) meta = M.do
  case (lookupTypeSignature sig x, es) of
    (Just ([<], idx), []) => M.do
      addSemanticToken (r0, ElimAnn)
      let omega = Typ.instantiateByElaboration omega meta (SignatureVarElim idx Terminal)
      return (Success omega [])
    (Just ([<], idx), _ :: _) => M.do
      return (Error "Type variable \{x} applied to a spine")
    (Just (_ :< _, idx), _) =>
      return (Error "Non-empty signature context not supported yet for name: \{x}")
    (Nothing, es) =>
      case (lookup x omega, es) of
        (Just (LetType [<] _), []) => M.do
          addSemanticToken (r0, ElimAnn)
          let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim x Terminal)
          return (Success omega [])
        (Just (LetType (_ :< _) _), _) => M.do
          return (Error "Non-empty signature context not supported yet for name: \{x}")
        (Just (LetType [<] _), _ :: _) => M.do
          return (Error "Type variable \{x} applied to a spine")
        _ => M.do
         (omega, t') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
         let omega = Typ.instantiateByElaboration omega meta (El (OmegaVarElim t' Id))
         return (Success omega [ElemElaboration ctx tm t' UniverseTy])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (OneVal x) _) meta = M.do
  return (Error "() is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (NatVal0 x) _) meta = M.do
  return (Error "Z is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (NatVal1 _) _) meta = M.do
  return (Error "S is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx tm@(App r (NatElim _) _) meta = M.do
  (omega, t') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (El (OmegaVarElim t' Id))
  return (Success omega [ElemElaboration ctx tm t' UniverseTy])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx tm@(App r (ZeroElim _) _) meta = M.do
  (omega, t') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (El (OmegaVarElim t' Id))
  return (Success omega [ElemElaboration ctx tm t' UniverseTy])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App _ (EqElim _) _) meta = M.do
  return (Error "J is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (EqVal x) _) meta = M.do
  return (Error "Refl is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (NatTy x) []) meta = M.do
  let omega = Typ.instantiateByElaboration omega meta NatTy
  return (Success omega [])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (NatTy x) _) meta =
  return (Error "ℕ applied to a wrong number of arguments")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (ZeroTy x) []) meta = M.do
  let omega = Typ.instantiateByElaboration omega meta ZeroTy
  return (Success omega [])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (ZeroTy x) _) meta =
  return (Error "𝟘 applied to a wrong number of arguments")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (OneTy x) []) meta = M.do
  let omega = Typ.instantiateByElaboration omega meta OneTy
  return (Success omega [])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (OneTy x) _) meta =
  return (Error "𝟙 applied to a wrong number of arguments")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (UniverseTy x) []) meta = M.do
  let omega = Typ.instantiateByElaboration omega meta UniverseTy
  return (Success omega [])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (UniverseTy x) _) meta =
  return (Error "𝕌 applied to a wrong number of arguments")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (UnnamedHole r0 Nothing) []) meta = M.do
  (omega, n) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim n Id)
  return (Success omega [])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (UnnamedHole r0 (Just vars)) []) meta = M.do
  let Just regctxPrefix = pickPrefix (cast ctx) vars
    | Nothing => return (Error "Invalid context prefix")
  let ctxPrefix = cast regctxPrefix
  (omega, n) <- liftUnifyM $ newTypeMeta omega ctxPrefix SolveByUnification
  let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim n (WkN (length ctx `minus` length regctxPrefix)))
  return (Success omega [])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (UnnamedHole x vars) _) meta =
  return (Error "? applied to arguments not supported")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (Hole r0 n Nothing) es) meta =
  case (lookup n omega) of
    Just _ => return (Error "Hole already exists: \{n}")
    Nothing => M.do
      omega <- liftUnifyM $ newTypeMeta omega ctx n NoSolve
      let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim n Id)
      addNamedHole (the Params %search).absFilePath r0 n
      return (Success omega [])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (Hole r0 n (Just vars)) es) meta =
  case (lookup n omega) of
    Just _ => return (Error "Hole already exists: \{n}")
    Nothing => M.do
      let Just regctxPrefix = pickPrefix (cast ctx) vars
        | Nothing => return (Error "Invalid context prefix")
      let ctxPrefix = cast regctxPrefix
      omega <- liftUnifyM $ newTypeMeta omega ctxPrefix n SolveByUnification
      let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim n (WkN (length ctx `minus` length regctxPrefix)))
      return (Success omega [])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (Unfold r0 x) _) meta = M.do
  return (Error "! is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx tm@(App r (PiBeta r0) _) meta = M.do
  return (Error "Π-β is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx tm@(App r (SigmaBeta1 r0) _) meta = M.do
  return (Error "Σ-β₁ is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx tm@(App r (SigmaBeta2 r0) _) meta = M.do
  return (Error "Σ-β₂ is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (PiEta r0) _) meta = M.do
  return (Error "Π-η is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (SigmaEta r0) _) meta = M.do
  return (Error "Σ-η is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (NatBetaZ r0) _) meta = M.do
  return (Error "ℕ-β-Z is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (NatBetaS r0) _) meta = M.do
  return (Error "ℕ-β-S is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (PiEq r0) _) meta = M.do
  return (Error "Π⁼ is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (SigmaEq r0) _) meta = M.do
  return (Error "Σ⁼ is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (OneEq r0) _) meta = M.do
  return (Error "𝟙⁼ is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (Tm _ tm) []) meta = M.do
  return (Success omega [TypeElaboration ctx tm meta])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (Tm _ tm) es) meta = M.do
  return (Error "_ _ is not a type")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (Tac r alpha) meta = M.do
  return (Error "tac is not supported in a type yet")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (Underscore r0) _) meta =
  return (Error "_ is not a valid term")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (Box r0) _) meta =
  return (Error "☐ is not a valid term")
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (El r0) [(_, Arg ([], el))]) meta = M.do
  -- ⟦e⟧ : 𝕌
  -- -------------------
  -- ⟦El e⟧ ⇝ El e' type
  (omega, el') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
  let omega = Typ.instantiateByElaboration omega meta (El (OmegaVarElim el' Id))
  return (Success omega [ElemElaboration ctx el el' UniverseTy])
Nova.Surface.Elaboration.Interface.elabType sig omega ctx (App r (El r0) _) meta = M.do
  return (Error "El applied to a wrong number of arguments")
