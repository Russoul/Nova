module Nova.Surface.Elaboration.Implementation.TopLevel

import Data.AVL
import Data.List
import Data.List1
import Data.Fin
import Data.Location
import Data.String

import Nova.Core.Context
import Nova.Core.Substitution
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Name
import Nova.Core.Pretty
import Nova.Core.Unification

import Nova.Surface.Language
import Nova.Surface.Shunting
import Nova.Surface.Operator
import Nova.Surface.SemanticToken

import Nova.Surface.Elaboration.Interface
import Nova.Surface.Elaboration.Pretty

||| Elaborates a top-level entry and adds it to the signature in case of success.
||| Throws on elaboration or unification error.
public export
elabTopLevelEntry : Params
                 => Signature
                 -> Omega
                 -> OpFreeTopLevel
                 -> ElabM (Either TopLevelError (Signature, Omega))
elabTopLevelEntry sig omega (TypingSignature r x ty) = M.do
  print_ Debug STDOUT "Elaborating \{x}"
  (omega, ty') <- liftUnifyM $ newTypeMeta omega [<] SolveByElaboration
  let probs = [TypeElaboration [<] ty ty']
  Success omega <- Interface.solve sig omega probs
    | Stuck omega stuckElab stuckCons => return (Left (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => return (Left (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => return (Left (UnificationError omega (con, err)))
  let sig = sig :< (x, ElemEntry [<] (OmegaVarElim ty' Id))
  let omega = subst omega Wk
  return (Right (sig, omega))
elabTopLevelEntry sig omega (LetSignature r x ty rhs) = M.do
  print_ Debug STDOUT "Elaborating \{x}"
  (omega, ty') <- liftUnifyM $ newTypeMeta omega [<] SolveByElaboration
  (omega, rhs') <- liftUnifyM $ newElemMeta omega [<] (OmegaVarElim ty' Id) SolveByElaboration
  let probs = [TypeElaboration [<] ty ty', ElemElaboration [<] rhs rhs' (OmegaVarElim ty' Id)]
  Success omega <- solve sig omega probs
    | Stuck omega stuckElab stuckCons => return (Left (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => return (Left (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => return (Left (UnificationError omega (con, err)))
  let sig = sig :< (x, LetElemEntry [<] (OmegaVarElim rhs' Id) (OmegaVarElim ty' Id))
  let omega = subst omega Wk
  return (Right (sig, omega))
elabTopLevelEntry sig omega (DefineSignature r x ty rhs) = M.do
  print_ Debug STDOUT "Elaborating \{x}"
  (omega, ty') <- liftUnifyM $ newTypeMeta omega [<] SolveByElaboration
  (omega, rhs') <- liftUnifyM $ newElemMeta omega [<] (OmegaVarElim ty' Id) SolveByElaboration
  let probs = [TypeElaboration [<] ty ty', ElemElaboration [<] rhs rhs' (OmegaVarElim ty' Id)]
  Success omega <- solve sig omega probs
    | Stuck omega stuckElab stuckCons => return (Left (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => return (Left (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => return (Left (UnificationError omega (con, err)))
  let omega = insert (x, LetElem [<] (OmegaVarElim rhs' Id) (OmegaVarElim ty' Id)) omega
  return (Right (sig, omega))
elabTopLevelEntry sig omega (LetTypeSignature r x rhs) = M.do
  print_ Debug STDOUT "Elaborating \{x}"
  (omega, rhs') <- liftUnifyM $ newTypeMeta omega [<] SolveByElaboration
  let probs = [TypeElaboration [<] rhs rhs']
  Success omega <- solve sig omega probs
    | Stuck omega stuckElab stuckCons => return (Left (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => return (Left (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => return (Left (UnificationError omega (con, err)))
  let sig = sig :< (x, LetTypeEntry [<] (OmegaVarElim rhs' Id))
  let omega = subst omega Wk
  return (Right (sig, omega))
elabTopLevelEntry sig omega (DefineTypeSignature r x rhs) = M.do
  print_ Debug STDOUT "Elaborating \{x}"
  (omega, rhs') <- liftUnifyM $ newTypeMeta omega [<] SolveByElaboration
  let probs = [TypeElaboration [<] rhs rhs']
  Success omega <- solve sig omega probs
    | Stuck omega stuckElab stuckCons => return (Left (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => return (Left (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => return (Left (UnificationError omega (con, err)))
  let omega = insert (x, LetType [<] (OmegaVarElim rhs' Id)) omega
  return (Right (sig, omega))

Nova.Surface.Elaboration.Interface.elabFile sig omega ops (Syntax r op ::: []) =
  return (Right (sig, omega, ops :< op))
Nova.Surface.Elaboration.Interface.elabFile sig omega ops (TypingSignature r x ty ::: []) = M.do
  -- write "Before shunting:\n\{show (TypingSignature r x ty)}"
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (TypingSignature r x ty))
    | Left err => return (Left (x, r, sig, err))
  return (Right (sig, omega, ops))
Nova.Surface.Elaboration.Interface.elabFile sig omega ops (LetSignature r x ty rhs ::: []) = M.do
  -- write "Before shunting:\n\{show (LetSignature r x ty rhs)}"
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (LetSignature r x ty rhs))
    | Left err => return (Left (x, r, sig, err))
  return (Right (sig, omega, ops))
Nova.Surface.Elaboration.Interface.elabFile sig omega ops (LetTypeSignature r x rhs ::: []) = M.do
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (LetTypeSignature r x rhs))
    | Left err => return (Left (x, r, sig, err))
  return (Right (sig, omega, ops))
Nova.Surface.Elaboration.Interface.elabFile sig omega ops (DefineTypeSignature r x rhs ::: []) = M.do
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (DefineTypeSignature r x rhs))
    | Left err => return (Left (x, r, sig, err))
  return (Right (sig, omega, ops))
Nova.Surface.Elaboration.Interface.elabFile sig omega ops (DefineSignature r x ty rhs ::: []) = M.do
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (DefineSignature r x ty rhs))
    | Left err => return (Left (x, r, sig, err))
  return (Right (sig, omega, ops))
Nova.Surface.Elaboration.Interface.elabFile sig omega ops (Syntax r op ::: e' :: es) = M.do
  Nova.Surface.Elaboration.Interface.elabFile sig omega (ops :< op) (e' ::: es)
Nova.Surface.Elaboration.Interface.elabFile sig omega ops (TypingSignature r x ty ::: e' :: es) = M.do
  -- write "Before shunting:\n\{show (TypingSignature r x ty)}"
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (TypingSignature r x ty))
    | Left err => return (Left (x, r, sig, err))
  Nova.Surface.Elaboration.Interface.elabFile sig omega ops (e' ::: es)
Nova.Surface.Elaboration.Interface.elabFile sig omega ops (LetSignature r x ty rhs ::: e' :: es) = M.do
  -- write "Before shunting:\n\{show (LetSignature r x ty rhs)}"
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (LetSignature r x ty rhs))
    | Left err => return (Left (x, r, sig, err))
  Nova.Surface.Elaboration.Interface.elabFile sig omega ops (e' ::: es)
Nova.Surface.Elaboration.Interface.elabFile sig omega ops (LetTypeSignature r x rhs ::: e' :: es) = M.do
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (LetTypeSignature r x rhs))
    | Left err => return (Left (x, r, sig, err))
  Nova.Surface.Elaboration.Interface.elabFile sig omega ops (e' ::: es)
Nova.Surface.Elaboration.Interface.elabFile sig omega ops (DefineSignature r x ty rhs ::: e' :: es) = M.do
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (DefineSignature r x ty rhs))
    | Left err => return (Left (x, r, sig, err))
  Nova.Surface.Elaboration.Interface.elabFile sig omega ops (e' ::: es)
Nova.Surface.Elaboration.Interface.elabFile sig omega ops (DefineTypeSignature r x rhs ::: e' :: es) = M.do
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (DefineTypeSignature r x rhs))
    | Left err => return (Left (x, r, sig, err))
  Nova.Surface.Elaboration.Interface.elabFile sig omega ops (e' ::: es)
