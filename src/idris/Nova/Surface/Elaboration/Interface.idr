module Nova.Surface.Elaboration.Interface

import Me.Russoul.Data.Location

import Data.AVL
import Data.List1

import Text.PrettyPrint.Prettyprinter

import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Name
import Nova.Core.Pretty
import Nova.Core.Unification

import Nova.Surface.Language
import Nova.Surface.Operator
import Nova.Surface.SemanticToken

CoreTyp = Nova.Core.Language.Typ.Typ
CoreElem = Nova.Core.Language.Elem.Elem
SurfaceTerm = Nova.Surface.Language.OpFreeTerm.OpFreeTerm

public export
record ElabSt where
  constructor MkElabSt
  unifySt : UnifySt
  toks : SnocList SemanticToken
  --              Absolute path        loc   meta idx
  namedHoles : OrdTree (String, List (Range, String)) ByFst

public export
record Params where
  [noHints] -- Make sure the machine won't try to synthesise an arbitrary element of that type when we %search
  constructor MkParams
  ||| Just the absolute path to the file we are currently elaborating.
  ||| Or nothing in case we are in interactive mode.
  absFilePath : Maybe String
  ||| Whether to solve named holes by unification (True) or not solve them at all (False).
  solveNamedHoles : Bool

public export
initialElabSt : ElabSt
initialElabSt = MkElabSt initialUnifySt [<] empty

||| The error type is a type represents critical unexpected unrecoverable errors.
||| By design, we are not supposed to ever try/catch those!
||| Don't use CriticalError for any other kind of error (e.g. recoverable / expected).
public export
ElabM : Type -> Type
ElabM = JustAMonad.M CriticalError ElabSt

namespace Elab
  public export
  liftM : M a -> ElabM a
  liftM f = M.do
    st <- get
    mapState (const st) (const ()) f

namespace ElabEither
  public export
  liftM : M a -> ElabM (Either e a)
  liftM f = M.do
    t <- Elab.liftM f
    return (Right t)

public export
liftUnifyM : UnifyM a -> ElabM a
liftUnifyM f = M.do
  MkElabSt _ toks namedHoles <- get
  mapState (\u => MkElabSt u toks namedHoles) (.unifySt) f

public export
liftUnifyM' : UnifyM a -> ElabM (Either e a)
liftUnifyM' f = M.do
  liftUnifyM f <&> Right

public export
addSemanticToken : SemanticToken -> ElabM ()
addSemanticToken t = update {toks $= (:< t)}

public export
addNamedHole : (absFilePath : String) -> (locInThatFile : Range) -> (idx : String) -> ElabM ()
addNamedHole path r idx = M.do
  holes <- get <&> namedHoles
  case lookup path holes of
    Nothing => update {namedHoles $= insert (path, [(r, idx)])}
    Just list => update {namedHoles $= insert (path, ((r, idx) :: list))}

public export
data ElaborationEntry : Type where
  ||| Γ ⊦ ⟦t⟧ ⇝ p : T
  ElemElaboration : Context -> SurfaceTerm -> OmegaName -> CoreTyp -> ElaborationEntry
  ||| Γ ⊦ ⟦A⟧ ⇝ A' type
  TypeElaboration : Context -> SurfaceTerm -> OmegaName -> ElaborationEntry
  ||| Γ ⊦ (t : T) ⟦ē⟧ ⇝ p : C
  ElemElimElaboration : Context -> CoreElem -> CoreTyp -> OpFreeElim -> OmegaName -> CoreTyp -> ElaborationEntry

public export
range : ElaborationEntry -> Range
range (ElemElaboration ctx tm n ty) = range tm
range (TypeElaboration ctx tm n) = range tm
range (ElemElimElaboration ctx head headTy [] n ty) = MkRange (0, 0) (0, 0) -- FIX: we need to come up with something in that case
range (ElemElimElaboration ctx head headTy ((r, _) :: _) n ty) = r

namespace Elaboration.Fixpoint
  public export
  data Fixpoint : Type where
    ||| We've solved all elaboration constraints, all unification problems and all unnamed holes.
    ||| Ω can only contain named holes and solved holes at this point.
    Success : Omega -> Fixpoint
    ||| We got stuck for good.
    ||| Ω might have changed, so we record the last one.
    Stuck : Omega -> List (ElaborationEntry, String) -> List (ConstraintEntry, String) -> Fixpoint
    ||| We hit a unification error or elaboration error.
    ||| Ω might have changed, so we record the last one.
    Error : Omega -> Either (ElaborationEntry, String) (ConstraintEntry, String) -> Fixpoint

namespace TopLevelError
    public export
    data TopLevelError : Type where
      Stuck : Omega -> List (ElaborationEntry, String) -> List (ConstraintEntry, String) -> TopLevelError
      UnificationError : Omega -> (ConstraintEntry, String) -> TopLevelError
      ElaborationError : Omega -> (ElaborationEntry, String) -> TopLevelError

namespace Elaboration
  public export
  data Result : Type where
    ||| Elaboration step has been made: new Ω that can contain new metas and new constraints.
    Success : Omega -> List ElaborationEntry -> Result
    ||| No elaboration step has been made.
    -- FIX: String ~> Doc Ann
    -- FIX: Add range?
    Stuck : String -> Result
    ||| Surface-level term can't be elaborated.
    -- FIX: String ~> Doc Ann
    -- FIX: Add range?
    Error : String -> Result

||| Try solving all elaboration and unification problems.
public export
solve : Params => SnocList Operator -> Signature -> Omega -> List ElaborationEntry -> ElabM Elaboration.Fixpoint.Fixpoint

||| Σ Ω Γ ⊦ ⟦t⟧ ⇝ p : A
public export
elabElem : Params
        => SnocList Operator
        -> Signature
        -> Omega
        -> Context
        -> SurfaceTerm
        -> OmegaName
        -> CoreTyp
        -> ElabM Elaboration.Result

||| Σ Ω Γ ⊦ ⟦A⟧ ⇝ A' type
||| Here we implicitly insert El to convert from 𝕌 to type
public export
elabType : Params
        => SnocList Operator
        -> Signature
        -> Omega
        -> Context
        -> SurfaceTerm
        -> OmegaName
        -> ElabM Elaboration.Result

||| Σ Ω Γ ⊦ (t : T) ⟦ē⟧ ⇝ t' : A
public export
elabElemElim : Params
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

||| Ξ Ω ⊦ ⟦α⟧ ⇝ α' : Σ₁ ⇒ Σ₀
-- FIX: elabTactic calls `solve` which, when fails, only shows stuck *local* elaboration problems. That is misleading!
public export
elabTactic : Params
          => SnocList Operator
          -> Signature
          -> Omega
          -> OpFreeTactic
          -> (target : Signature)
          -> ElabM (Either (Range, Doc Ann) (Omega, Signature, SignatureInst -> SignatureInst))

||| Elaborate a .nova file parsed in advance.
public export
elabFile : Params
        => SnocList Operator
        -> Signature
        -> Omega
        -> List1 TopLevel
        --                vvvvvv def name
        --                        vvvvv def range
        --                               vvvvvvvvv elaborated so far
        -> ElabM (Either (String, Range, Signature, TopLevelError) (SnocList Operator, Signature, Omega))
