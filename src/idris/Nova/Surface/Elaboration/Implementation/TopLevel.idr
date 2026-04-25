module Nova.Surface.Elaboration.Implementation.TopLevel

import Me.Russoul.Data.Location

import Nova.Control.Monad.Id
import Nova.Control.Monad.St
import Nova.Control.Monad.StEither

import Data.AVL
import Data.List
import Data.List1
import Data.Fin
import Data.String

import Nova.Core.Context
import Nova.Core.Substitution
import Nova.Core.Language
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
                 => SnocList Operator
                 -> Signature
                 -> Omega
                 -> OpFreeTopLevel
                 -> ElabM (Either TopLevelError (Signature, Omega))
elabTopLevelEntry ops sig omega (TypingSignature r x ty) = StEither.do
  -- print_ Debug STDOUT "Elaborating \{x}"
  (omega, ty') <- liftUnifyM' $ newTypeMeta omega [<] SolveByElaboration
  let probs = [TypeElaboration [<] ty ty']
  Success omega <- StEither.liftSt $ Interface.solve ops sig omega probs
    | Stuck omega stuckElab stuckCons => throw (Stuck omega stuckElab stuckCons)
    | Error omega (Left (elab, err)) => throw (ElaborationError omega (elab, err))
    | Error omega (Right (con, err)) => throw (UnificationError omega (con, err))
  let sig = sig :< (x, ElemEntry [<] (OmegaVarElim ty' Id))
  let omega = subst omega Wk
  pure (sig, omega)
elabTopLevelEntry ops sig omega (LetSignature r x ty rhs) = StEither.do
  -- print_ Debug STDOUT "Elaborating \{x}"
  (omega, ty') <- liftUnifyM' $ newTypeMeta omega [<] SolveByElaboration
  (omega, rhs') <- liftUnifyM' $ newElemMeta omega [<] (OmegaVarElim ty' Id) SolveByElaboration
  let probs = [TypeElaboration [<] ty ty', ElemElaboration [<] rhs rhs' (OmegaVarElim ty' Id)]
  Success omega <- StEither.liftSt $ solve ops sig omega probs
    | Stuck omega stuckElab stuckCons => throw (Stuck omega stuckElab stuckCons)
    | Error omega (Left (elab, err)) => throw (ElaborationError omega (elab, err))
    | Error omega (Right (con, err)) => throw (UnificationError omega (con, err))
  let sig = sig :< (x, LetElemEntry [<] (OmegaVarElim rhs' Id) (OmegaVarElim ty' Id))
  let omega = subst omega Wk
  pure (sig, omega)
elabTopLevelEntry ops sig omega (DefineSignature r x ty rhs) = StEither.do
  -- print_ Debug STDOUT "Elaborating \{x}"
  (omega, ty') <- liftUnifyM' $ newTypeMeta omega [<] SolveByElaboration
  (omega, rhs') <- liftUnifyM' $ newElemMeta omega [<] (OmegaVarElim ty' Id) SolveByElaboration
  let probs = [TypeElaboration [<] ty ty', ElemElaboration [<] rhs rhs' (OmegaVarElim ty' Id)]
  Success omega <- StEither.liftSt $ solve ops sig omega probs
    | Stuck omega stuckElab stuckCons => throw (Stuck omega stuckElab stuckCons)
    | Error omega (Left (elab, err)) => throw (ElaborationError omega (elab, err))
    | Error omega (Right (con, err)) => throw (UnificationError omega (con, err))
  let omega = insert (x, LetElem [<] (OmegaVarElim rhs' Id) (OmegaVarElim ty' Id)) omega
  pure (sig, omega)
elabTopLevelEntry ops sig omega (LetTypeSignature r x rhs) = StEither.do
  -- print_ Debug STDOUT "Elaborating \{x}"
  (omega, rhs') <- liftUnifyM' $ newTypeMeta omega [<] SolveByElaboration
  let probs = [TypeElaboration [<] rhs rhs']
  Success omega <- StEither.liftSt $ solve ops sig omega probs
    | Stuck omega stuckElab stuckCons => throw (Stuck omega stuckElab stuckCons)
    | Error omega (Left (elab, err)) => throw (ElaborationError omega (elab, err))
    | Error omega (Right (con, err)) => throw (UnificationError omega (con, err))
  let sig = sig :< (x, LetTypeEntry [<] (OmegaVarElim rhs' Id))
  let omega = subst omega Wk
  pure (sig, omega)
elabTopLevelEntry ops sig omega (DefineTypeSignature r x rhs) = StEither.do
  -- print_ Debug STDOUT "Elaborating \{x}"
  (omega, rhs') <- liftUnifyM' $ newTypeMeta omega [<] SolveByElaboration
  let probs = [TypeElaboration [<] rhs rhs']
  Success omega <- StEither.liftSt $ solve ops sig omega probs
    | Stuck omega stuckElab stuckCons => throw (Stuck omega stuckElab stuckCons)
    | Error omega (Left (elab, err)) => throw (ElaborationError omega (elab, err))
    | Error omega (Right (con, err)) => throw (UnificationError omega (con, err))
  let omega = insert (x, LetType [<] (OmegaVarElim rhs' Id)) omega
  pure (sig, omega)

export
expect : Either String a -> a
expect (Left err) = assert_total $ idris_crash err
expect (Right x) = x

elabTopLevelSyn : Params
               => SnocList Operator
               -> Signature
               -> Omega
               -> TopLevel
               --                vvvvvv def name
               --                        vvvvv def range
               --                               vvvvvvvvv elaborated so far
               -> ElabM (Either (String, Range, Signature, TopLevelError) (SnocList Operator, Signature, Omega))
elabTopLevelSyn ops sig omega (Syntax r op) =
  StEither.pure (ops :< op, sig, omega)
elabTopLevelSyn ops sig omega (TypingSignature r x ty) = StEither.do
  -- write "Before shunting:\n\{show (TypingSignature r x ty)}"
  -- FIX:                               vvvvvv shouldn't be critical error
  (sig, omega) <- mapError (x, r, sig,)
    $ elabTopLevelEntry ops sig omega (expect $ shuntTopLevel (cast ops) (TypingSignature r x ty))
  pure (ops, sig, omega)
elabTopLevelSyn ops sig omega (LetSignature r x ty rhs) = StEither.do
  -- write "Before shunting:\n\{show (LetSignature r x ty rhs)}"
  (sig, omega) <- mapError (x, r, sig,)
    $ elabTopLevelEntry ops sig omega (expect $ shuntTopLevel (cast ops) (LetSignature r x ty rhs))
  pure (ops, sig, omega)
elabTopLevelSyn ops sig omega (LetTypeSignature r x rhs) = StEither.do
  (sig, omega) <- mapError (x, r, sig,)
    $ elabTopLevelEntry ops sig omega (expect $ shuntTopLevel (cast ops) (LetTypeSignature r x rhs))
  pure (ops, sig, omega)
elabTopLevelSyn ops sig omega (DefineTypeSignature r x rhs) = StEither.do
  (sig, omega) <- mapError (x, r, sig,)
    $ elabTopLevelEntry ops sig omega (expect $ shuntTopLevel (cast ops) (DefineTypeSignature r x rhs))
  pure (ops, sig, omega)
elabTopLevelSyn ops sig omega (DefineSignature r x ty rhs) = StEither.do
  (sig, omega) <- mapError (x, r, sig,)
    $ elabTopLevelEntry ops sig omega (expect $ shuntTopLevel (cast ops) (DefineSignature r x ty rhs))
  pure (ops, sig, omega)

Nova.Surface.Elaboration.Interface.elabFile ops sig omega (def ::: []) = StEither.do
  elabTopLevelSyn ops sig omega def
Nova.Surface.Elaboration.Interface.elabFile ops sig omega (def ::: def' :: more) = StEither.do
  (ops, sig, omega) <- elabTopLevelSyn ops sig omega def
  Nova.Surface.Elaboration.Interface.elabFile ops sig omega (def' ::: more)
