module Nova.Surface.Elaboration.Implementation.Solve

import Me.Russoul.Data.Location

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

import Nova.Surface.Elaboration.Implementation.Common
import Nova.Surface.Elaboration.Implementation.Elem
import Nova.Surface.Elaboration.Implementation.Tactic.Trivial
import Nova.Surface.Elaboration.Implementation.Tactic.Unfold
import Nova.Surface.Elaboration.Implementation.Typ
import Nova.Surface.Elaboration.Interface
import Nova.Surface.Elaboration.Pretty

--TODO: We just insert some logging for debug here
public export
elabEntry : Params
         => SnocList Operator
         -> Signature
         -> Omega
         -> ElaborationEntry
         -> ElabM Elaboration.Result
elabEntry ops sig omega entry = M.do
  let go : Signature
        -> Omega
        -> ElaborationEntry
        -> ElabM Elaboration.Result
      go sig omega (ElemElaboration ctx tm p ty) =
        elabElem ops sig omega ctx tm p ty
      go sig omega (TypeElaboration ctx tm p) =
        elabType ops sig omega ctx tm p
      go sig omega (ElemElimElaboration ctx head headTy es p ty) =
        elabElemElim ops sig omega ctx head headTy es p ty
  result <- go sig omega entry
  {- print_ Debug STDOUT "--------- Elaborating ---------"
  print_ Debug STDOUT (renderDocTerm !(liftM $ pretty sig omega entry))
  print_ Debug STDOUT "Result:"
  print_ Debug STDOUT (renderDocTerm !(liftM $ prettyResult sig result))
  print_ Debug STDOUT "-------------------------------" -}
  return result

||| The intermediate results of solving a list of constraints (reflects whether at least some progress has been made).
public export
data IntermediateResult : Type where
  ||| We've traversed the list of pending elaboration problems once.
  ||| At least one step has been made.
  ||| We store a new Ω that can contain new holes and new constraints.
  ||| We store the list of problems to solve.
  Success : Omega -> List (ElaborationEntry, String) -> IntermediateResult
  ||| We haven't progressed at all.
  Stuck : List (ElaborationEntry, String) -> IntermediateResult
  ||| We've hit an error.
  Error : ElaborationEntry -> String -> IntermediateResult

progressEntriesH : Params
                => SnocList Operator
                -> Signature
                -> Omega
                -> (stuck : SnocList (ElaborationEntry, String))
                -> List ElaborationEntry
                -> Bool
                -> ElabM IntermediateResult
progressEntriesH ops sig cs stuck [] False = return (Stuck (cast stuck))
progressEntriesH ops sig cs stuck [] True = return (Success cs (cast stuck))
progressEntriesH ops sig cs stuck (e :: es) progressMade =
  case !(elabEntry ops sig cs e) of
    Success cs' new => progressEntriesH ops sig cs' stuck (new ++ es) True
    Stuck reason => progressEntriesH ops sig cs (stuck :< (e, reason)) es progressMade
    Error str => return (Error e str)

progressEntries : Params
               => SnocList Operator
               -> Signature
               -> Omega
               -> List ElaborationEntry
               -> ElabM IntermediateResult
progressEntries ops sig cs list = progressEntriesH ops sig cs [<] list False

||| Try solving the problems in the list until either no constraints are left or each and every one is stuck.
||| Between rounds of solving problems we try solving unification problems.
progressEntriesFixpoint : Params => SnocList Operator -> Signature -> Omega -> List ElaborationEntry -> ElabM Elaboration.Fixpoint.Fixpoint
progressEntriesFixpoint ops sig cs todo = M.do
  case containsNamedHolesOnly cs && isNil todo of
    True => return (Success cs)
    False => M.do
      case !(progressEntries ops sig cs todo) of
        Stuck stuckElaborations => M.do
          case !(liftUnifyM $ Unification.solve sig cs) of
            Stuck stuckConstraints => return (Stuck cs stuckElaborations stuckConstraints)
            Disunifier e err => return (Error cs (Right (e, err)))
            Success cs => progressEntriesFixpoint ops sig cs todo
        Error e str => return (Error cs (Left (e, str)))
        Success cs todo => progressEntriesFixpoint ops sig cs (map fst todo)

Nova.Surface.Elaboration.Interface.solve ops sig omega todo = progressEntriesFixpoint ops sig omega todo

