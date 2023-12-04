module Nova.Surface.Elaboration

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
import Nova.Core.FreeVariable
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

import Nova.Surface.Tactic.Reduce
import Nova.Surface.Tactic.Trivial

CoreTyp = Nova.Core.Language.D.Typ
CoreElem = Nova.Core.Language.E.Elem
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
  ||| Absolute path to a file we are currently elaborating.
  absFilePath : String

public export
initialElabSt : ElabSt
initialElabSt = MkElabSt initialUnifySt [<] empty

public export
ElabM : Type -> Type
ElabM = JustAMonad.M String ElabSt

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
liftMEither : M (Either String a) -> ElabM a
liftMEither f = M.do
 case !(Elab.liftM f) of
   Right x => return x
   Left err => throw err

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

partial
public export
Show ElaborationEntry where
  show (ElemElaboration ctx tm p ty) = "... ⊦ ⟦\{show tm}⟧ ⇝ ... : ..."
  show (TypeElaboration ctx tm p) = "... ⊦ ⟦\{show tm}⟧ ⇝ ... type"
  show (ElemElimElaboration ctx head headTy tm meta ty) = "... ⊦ (... : ...) ⟦\{show tm}⟧ ⇝ ... : ..."

namespace ElaborationEntry
  public export
  pretty : Signature -> Omega -> ElaborationEntry -> M (Doc Ann)
  pretty sig omega (ElemElaboration ctx tm p ty) = M.do
    return $
      !(prettyContext sig omega ctx)
      <++>
      "⊦"
      <++>
      "⟦"
      <+>
      pretty (show tm)
      <+>
      "⟧"
      <++>
      "⇝"
      <++>
      pretty p
      <++>
      ":"
      <++>
      !(prettyTyp sig omega (map fst ctx) ty 0)
  pretty sig omega (TypeElaboration ctx tm p) = M.do
    return $
      !(prettyContext sig omega ctx)
      <++>
      "⊦"
      <++>
      "⟦"
      <+>
      pretty (show tm)
      <+>
      "⟧"
      <++>
      "⇝"
      <++>
      pretty p
      <++>
      "type"
  pretty sig omega (ElemElimElaboration ctx head headTy tm p ty) = M.do
    return $
      !(prettyContext sig omega ctx)
      <++>
      "⊦"
      <++>
      "("
      <+>
      !(prettyElem sig omega (map fst ctx) head 0)
      <++>
      ":"
      <++>
      !(prettyTyp sig omega (map fst ctx) headTy 0)
      <+>
      ")"
      <++>
      "⟦"
      <+>
      pretty (show tm)
      <+>
      "⟧"
      <++>
      "⇝"
      <++>
      pretty p
      <++>
      ":"
      <++>
      !(prettyTyp sig omega (map fst ctx) ty 0)

namespace TopLevelError
    public export
    data TopLevelError : Type where
      Stuck : Omega -> List (ElaborationEntry, String) -> List (ConstraintEntry, String) -> TopLevelError
      UnificationError : Omega -> (ConstraintEntry, String) -> TopLevelError
      ElaborationError : Omega -> (ElaborationEntry, String) -> TopLevelError

    public export
    pretty : Signature -> TopLevelError -> M (Doc Ann)
    pretty sig (Stuck omega stuckElab stuckCons) = M.do
      let unsolvedMetas = filter (\(_, x) => isMetaType x || isMetaElem x) (List.inorder omega)
      return $
        pretty "----------- Stuck unification constraints (#\{show (length stuckCons)}): -------------"
         <+>
        hardline
         <+>
        vsep !(forList stuckCons $ \(con, str) => M.do
               return $
                 !(prettyConstraintEntry sig omega con)
                  <+>
                 hardline
                  <+>
                 pretty "Reason: \{str}"
              )
         <+>
        hardline
         <+>
        pretty "----------- Unsolved meta variables (#\{show (length unsolvedMetas)}): -------------"
         <+>
        hardline
         <+>
        !(prettyOmega' sig omega unsolvedMetas)
         <+>
        hardline
         <+>
        pretty "----------- Stuck elaboration constraints (#\{show (length stuckElab)}): -------------"
         <+>
        hardline
         <+>
        vsep !(forList stuckElab $ \(elab, err) => M.do
          return $
            !(pretty sig omega elab)
             <+>
            hardline
             <+>
            pretty "Reason: \{err}")
    pretty sig (UnificationError omega (con, err)) = M.do
      return $
        "----------- Disunifier found: -------------"
         <+>
        hardline
         <+>
        !(prettyConstraintEntry sig omega con)
         <+>
        hardline
         <+>
        pretty "Reason: \{err}"
    pretty sig (ElaborationError omega (elab, err)) = M.do
      return $
         "----------- Elaborator failed: -------------"
          <+>
         hardline
          <+>
         pretty (show elab)
          <+>
         hardline
          <+>
         pretty "Reason: \{err}"




public export
range : ElaborationEntry -> Range
range (ElemElaboration ctx tm n ty) = range tm
range (TypeElaboration ctx tm n) = range tm
range (ElemElimElaboration ctx head headTy [] n ty) = MkRange (0, 0) (0, 0) -- FIX: we need to come up with something in that case
range (ElemElimElaboration ctx head headTy ((r, _) :: _) n ty) = r

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

namespace Typ
  public export
  instantiateByElaboration : Omega -> OmegaName -> Typ -> Omega
  instantiateByElaboration omega idx rhs =
    case (lookup idx omega) of
      Just (MetaType ctx SolveByElaboration) => insert (idx, LetType ctx rhs) omega
      _ => assert_total $ idris_crash "instantiateByElaboration"

namespace Elem
  public export
  instantiateByElaboration : Omega -> OmegaName -> Elem -> Omega
  instantiateByElaboration omega idx rhs =
    case (lookup idx omega) of
      Just (MetaElem ctx ty SolveByElaboration) => insert (idx, LetElem ctx rhs ty) omega
      _ => assert_total $ idris_crash "instantiateByElaboration"

||| Γ₀ (xᵢ : A) Γ₁ ⊦ xᵢ : A
lookupContext : Context -> VarName -> Maybe (CoreElem, CoreTyp)
lookupContext [<] x = Nothing
lookupContext (ctx :< (x, ty)) y = M.do
  case x == y of
    True => Just (ContextVarElim 0, ContextSubstElim ty Wk)
    False => do
      (t, ty) <- lookupContext ctx y
      Just (ContextSubstElim t Wk, ContextSubstElim ty Wk)

public export
pickPrefix : List (VarName, Typ) -> List VarName -> Maybe (List (VarName, Typ))
pickPrefix ctx [] = Just []
pickPrefix [] (x :: xs) = Nothing
pickPrefix ((x', ty) :: ctx) (x :: xs) =
  case (x' == x) of
    True => pickPrefix ctx xs <&> ((x, ty) ::)
    False => Nothing

mutual
  ||| Σ Ω Γ ⊦ ⟦t⟧ ⇝ p : A
  ||| A is head-neutral w.r.t. open evaluation.
  public export
  elabElemNu : Params
            => Signature
            -> Omega
            -> Context
            -> SurfaceTerm
            -> OmegaName
            -> CoreTyp
            -> ElabM Elaboration.Result
  elabElemNu sig omega ctx (PiTy r x dom cod) meta UniverseTy = M.do
    (omega, dom') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    (omega, cod') <- liftUnifyM $ newElemMeta omega (ctx :< (x, El $ OmegaVarElim dom' Id)) UniverseTy SolveByElaboration
    let omega = Elem.instantiateByElaboration omega meta (PiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
    return (Success omega [ElemElaboration ctx dom dom' UniverseTy, ElemElaboration (ctx :< (x, El $ OmegaVarElim dom' Id)) cod cod' UniverseTy])
  elabElemNu sig omega ctx tm@(PiTy r x dom cod) meta ty = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
    return (Success omega [ElemElaboration ctx tm meta UniverseTy])
  elabElemNu sig omega ctx (ImplicitPiTy r x dom cod) meta UniverseTy = M.do
    (omega, dom') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    (omega, cod') <- liftUnifyM $ newElemMeta omega (ctx :< (x, El $ OmegaVarElim dom' Id)) UniverseTy SolveByElaboration
    let omega = Elem.instantiateByElaboration omega meta (ImplicitPiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
    return (Success omega [ElemElaboration ctx dom dom' UniverseTy, ElemElaboration (ctx :< (x, El $ OmegaVarElim dom' Id)) cod cod' UniverseTy])
  elabElemNu sig omega ctx tm@(ImplicitPiTy r x dom cod) meta ty = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
    return (Success omega [ElemElaboration ctx tm meta UniverseTy])
  elabElemNu sig omega ctx (SigmaTy r x dom cod) meta UniverseTy = M.do
    (omega, dom') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    (omega, cod') <- liftUnifyM $ newElemMeta omega (ctx :< (x, El $ OmegaVarElim dom' Id)) UniverseTy SolveByElaboration
    let omega = Elem.instantiateByElaboration omega meta (SigmaTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
    return (Success omega [ElemElaboration ctx dom dom' UniverseTy, ElemElaboration (ctx :< (x, El $ OmegaVarElim dom' Id)) cod cod' UniverseTy])
  elabElemNu sig omega ctx tm@(SigmaTy r x dom cod) meta ty = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
    return (Success omega [ElemElaboration ctx tm meta UniverseTy])
  elabElemNu sig omega ctx (FunTy r dom cod) meta UniverseTy = M.do
    (omega, dom') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    (omega, cod') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    let omega = Elem.instantiateByElaboration omega meta (PiTy "_" (OmegaVarElim dom' Id) (OmegaVarElim cod' Wk))
    return (Success omega [ElemElaboration ctx dom dom' UniverseTy, ElemElaboration ctx cod cod' UniverseTy])
  elabElemNu sig omega ctx tm@(FunTy x y z) meta ty = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
    return (Success omega [ElemElaboration ctx tm meta UniverseTy])
  elabElemNu sig omega ctx (ProdTy r dom cod) meta UniverseTy = M.do
    (omega, dom') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    (omega, cod') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    let omega = Elem.instantiateByElaboration omega meta (SigmaTy "_" (OmegaVarElim dom' Id) ((OmegaVarElim cod' Wk)))
    return (Success omega [ElemElaboration ctx dom dom' UniverseTy, ElemElaboration ctx cod cod' UniverseTy])
  elabElemNu sig omega ctx tm@(ProdTy x y z) meta ty = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
    return (Success omega [ElemElaboration ctx tm meta UniverseTy])
  elabElemNu sig omega ctx (TyEqTy r a b) meta UniverseTy = M.do
    (omega, a') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    (omega, b') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    let omega = Elem.instantiateByElaboration omega meta (TyEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id))
    return (Success omega [ ElemElaboration ctx a a' UniverseTy,
                            ElemElaboration ctx b b' UniverseTy
                          ]
           )
  elabElemNu sig omega ctx tm@(TyEqTy r a b) meta ty = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
    return (Success omega [ElemElaboration ctx tm meta UniverseTy])
  elabElemNu sig omega ctx (ElEqTy r a b t) meta UniverseTy = M.do
    (omega, t') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    (omega, a') <- liftUnifyM $ newElemMeta omega ctx (El $ OmegaVarElim t' Id) SolveByElaboration
    (omega, b') <- liftUnifyM $ newElemMeta omega ctx (El $ OmegaVarElim t' Id) SolveByElaboration
    let omega = Elem.instantiateByElaboration omega meta (ElEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) (OmegaVarElim t' Id))
    return (Success omega [ElemElaboration ctx t t' UniverseTy,
                           ElemElaboration ctx a a' (El $ OmegaVarElim t' Id),
                           ElemElaboration ctx b b' (El $ OmegaVarElim t' Id)
                          ]
           )
  elabElemNu sig omega ctx tm@(ElEqTy r a b t) meta ty = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
    return (Success omega [ElemElaboration ctx tm meta UniverseTy])
  elabElemNu sig omega ctx (PiVal r x f) meta (PiTy _ dom cod) = M.do
    (omega, f') <- liftUnifyM $ newElemMeta omega (ctx :< (x, dom)) cod SolveByElaboration
    let omega = Elem.instantiateByElaboration omega meta (PiVal x dom cod (OmegaVarElim f' Id))
    return (Success omega [ElemElaboration (ctx :< (x, dom)) f f' cod])
  elabElemNu sig omega ctx tm@(PiVal r x f) meta ty = M.do
    (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
    (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom Id)) SolveByUnification
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty (PiTy x (OmegaVarElim dom Id) (OmegaVarElim cod Id)))
    return (Success omega [ElemElaboration ctx tm meta (PiTy x (OmegaVarElim dom Id) (OmegaVarElim cod Id))])
  elabElemNu sig omega ctx (ImplicitPiVal r x f) meta (ImplicitPiTy _ dom cod) = M.do
    (omega, f') <- liftUnifyM $ newElemMeta omega (ctx :< (x, dom)) cod SolveByElaboration
    let omega = Elem.instantiateByElaboration omega meta (ImplicitPiVal x dom cod (OmegaVarElim f' Id))
    return (Success omega [ElemElaboration (ctx :< (x, dom)) f f' cod])
  elabElemNu sig omega ctx tm@(ImplicitPiVal r x f) meta ty = M.do
    (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
    (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom Id)) SolveByUnification
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty (ImplicitPiTy x (OmegaVarElim dom Id) (OmegaVarElim cod Id)))
    return (Success omega [ElemElaboration ctx tm meta (ImplicitPiTy x (OmegaVarElim dom Id) (OmegaVarElim cod Id))])
  elabElemNu sig omega ctx (SigmaVal r a b) meta (SigmaTy _ dom cod) = M.do
    (omega, a') <- liftUnifyM $ newElemMeta omega ctx dom SolveByElaboration
    (omega, b') <- liftUnifyM $ newElemMeta omega ctx (ContextSubstElim cod (Ext Id (OmegaVarElim a' Id))) SolveByElaboration
    let omega = Elem.instantiateByElaboration omega meta (SigmaVal (OmegaVarElim a' Id) (OmegaVarElim b' Id))
    return (Success omega [ElemElaboration ctx a a' dom, ElemElaboration ctx b b' (ContextSubstElim cod (Ext Id (OmegaVarElim a' Id)))])
  elabElemNu sig omega ctx tm@(SigmaVal r a b) meta ty = M.do
    (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
    (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< ("_", OmegaVarElim dom Id)) SolveByUnification
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)))
    return (Success omega [ElemElaboration ctx tm meta (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))])
  elabElemNu sig omega ctx (App r (Var r0 x) es) meta ty = M.do
    case lookupContext ctx x of
      Just (vTm, vTy) => M.do
        addSemanticToken (r0, BoundVarAnn)
        return (Success omega [ElemElimElaboration ctx vTm vTy es meta ty])
      Nothing =>
        case lookupSignature sig x of
          Just ([<], idx, vTy) => M.do
            addSemanticToken (r0, ElimAnn)
            return (Success omega [ElemElimElaboration ctx (SignatureVarElim idx Terminal) vTy es meta ty])
          Just (sigCtx, idx, ty) =>
            return (Error "Non-empty signature context not supported yet for name: \{x}")
          Nothing =>
            case lookup x omega of
              Just (LetElem [<] _ vTy) => M.do
                addSemanticToken (r0, ElimAnn)
                return (Success omega [ElemElimElaboration ctx (OmegaVarElim x Terminal) vTy es meta ty])
              _ => return (Error "Undefined name: \{x}")
  elabElemNu sig omega ctx (App r (NatVal0 x) []) meta NatTy = M.do
    let omega = Elem.instantiateByElaboration omega meta NatVal0
    return (Success omega [])
  elabElemNu sig omega ctx tm@(App r (NatVal0 x) []) meta ty = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty NatTy)
    return (Success omega [ElemElaboration ctx tm meta NatTy])
  elabElemNu sig omega ctx (App r (NatVal0 x) (_ :: _)) meta ty =
    return (Error "Z applied to a spine")
  elabElemNu sig omega ctx (App r (OneVal x) []) meta OneTy = M.do
    let omega = Elem.instantiateByElaboration omega meta OneVal
    return (Success omega [])
  elabElemNu sig omega ctx tm@(App r (OneVal x) []) meta ty = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty OneTy)
    return (Success omega [ElemElaboration ctx tm meta OneTy])
  elabElemNu sig omega ctx (App r (OneVal x) (_ :: _)) meta ty =
    return (Error "tt applied to a spine")
  elabElemNu sig omega ctx (App r (NatVal1 _) [(_, Arg ([], t))]) meta NatTy = M.do
    (omega, t') <- liftUnifyM $ newElemMeta omega ctx NatTy SolveByElaboration
    let omega = Elem.instantiateByElaboration omega meta (NatVal1 (OmegaVarElim t' Id))
    return (Success omega [ElemElaboration ctx t t' NatTy])
  elabElemNu sig omega ctx tm@(App r (NatVal1 _) [t]) meta ty = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty NatTy)
    return (Success omega [ElemElaboration ctx tm meta NatTy])
  elabElemNu sig omega ctx (App r (NatVal1 x) _) meta ty =
    return (Error "S applied to a wrong number of arguments")
  elabElemNu sig omega ctx (App r (NatElim _) ((_, Arg ([x], schema)) :: (_, Arg ([], z)) :: (_, Arg ([y, h], s)) :: (_, Arg ([], t)) :: es)) meta ty = M.do
    (omega, schema') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, NatTy)) SolveByElaboration
    (omega, z') <- liftUnifyM $ newElemMeta omega ctx (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)) SolveByElaboration
    (omega, s') <- liftUnifyM $ newElemMeta omega (ctx :< (y, NatTy) :< (h, OmegaVarElim schema' Id))
                                    (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))) SolveByElaboration
    (omega, t') <- liftUnifyM $ newElemMeta omega ctx NatTy SolveByElaboration
    return (Success omega [TypeElaboration (ctx :< (x, NatTy)) schema schema',
                           ElemElaboration ctx z z' (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)),
                           ElemElaboration (ctx :< (y, NatTy) :< (h, OmegaVarElim schema' Id)) s s' (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))),
                           ElemElaboration ctx t t' NatTy,
                           ElemElimElaboration ctx (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) (OmegaVarElim t' Id)) (OmegaVarElim schema' (Ext Id (OmegaVarElim t' Id))) es meta ty])
  elabElemNu sig omega ctx (App r (NatElim _) _) meta ty =
    return (Error "ℕ-elim applied to a wrong number of arguments")
  elabElemNu sig omega ctx (App r (ZeroElim _) ((_, Arg ([], t)) :: es)) meta ty = M.do
    (omega, t') <- liftUnifyM $ newElemMeta omega ctx ZeroTy SolveByElaboration
    return (Success omega [ElemElaboration ctx t t' ZeroTy,
                           ElemElimElaboration ctx (ZeroElim (OmegaVarElim t' Id)) ty es meta ty])
  elabElemNu sig omega ctx (App r (ZeroElim _) _) meta ty =
    return (Error "𝟘-elim applied to a wrong number of arguments")
  elabElemNu sig omega ctx (App _ (EqElim _) ((_, Arg ([], elemTy)) :: (_, Arg ([], a0)) :: (_, Arg ([x, h], schema)) :: (_, Arg ([], r)) :: (_, Arg ([], a1)) :: (_, Arg ([], e)) :: es)) meta ty = M.do
    (omega, t') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
    (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
    (omega, schema') <- liftUnifyM $ newTypeMeta omega ((ctx :< (x, OmegaVarElim t' Id)) :< (h, ElEqTy (ContextSubstElim (OmegaVarElim a' Id) Wk) CtxVar (ContextSubstElim (OmegaVarElim t' Id) Wk))) SolveByElaboration
    (omega, r') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim schema' (Ext (Ext Id (OmegaVarElim a' Id)) ElEqVal)) SolveByElaboration
    (omega, e') <- liftUnifyM $ newElemMeta omega ctx (ElEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) (OmegaVarElim t' Id)) SolveByElaboration
    return (Success omega [TypeElaboration ctx elemTy t',
                           ElemElaboration ctx a0 a' (OmegaVarElim t' Id),
                           ElemElaboration ctx a1 b' (OmegaVarElim t' Id),
                           ElemElaboration ctx e e' (ElEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) (OmegaVarElim t' Id)),
                           TypeElaboration (ctx :< (x, OmegaVarElim t' Id) :< (h, (ElEqTy (ContextSubstElim (OmegaVarElim a' Id) Wk) CtxVar (ContextSubstElim (OmegaVarElim t' Id) Wk)))) schema schema',
                           ElemElaboration ctx r r' (OmegaVarElim schema' (Ext (Ext Id (OmegaVarElim a' Id)) ElEqVal)),
                           ElemElimElaboration ctx (OmegaVarElim r' Id) (OmegaVarElim schema' (Ext (Ext Id (OmegaVarElim b' Id)) (OmegaVarElim e' Id))) es meta ty])
  elabElemNu sig omega ctx (App r (EqElim x) _) meta ty =
    return (Error "J applied to a wrong number of arguments")
  elabElemNu sig omega ctx (App r (EqVal x) []) meta (TyEqTy a b) = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx a b)
    let omega = Elem.instantiateByElaboration omega meta TyEqVal
    return (Success omega [])
  elabElemNu sig omega ctx (App r (EqVal x) []) meta (ElEqTy a b t) = M.do
    omega <- liftUnifyM $ addConstraint omega (ElemConstraint ctx a b t)
    let omega = Elem.instantiateByElaboration omega meta ElEqVal
    return (Success omega [])
  elabElemNu sig omega ctx tm@(App r (EqVal x) []) meta ty = M.do
    -- We can have one of:
    --   ⟦Refl⟧ : (? ≡ ? ∈ ?)
    --   ⟦Refl⟧ : (? ≡ ? type)
    -- Can't decide yet
    return (Stuck "Refl : _")
    {- (omega, t') <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
    (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByUnification
    (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByUnification
    let t = OmegaVarElim t' Id
    let a = OmegaVarElim a' Id
    let b = OmegaVarElim b' Id
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty (EqTy a b t))
    return (Success omega [ElemElaboration ctx tm meta (EqTy a b t)]) -}
  elabElemNu sig omega ctx (App r (EqVal x) _) meta ty = M.do
    return (Error "Refl applied to wrong number of arguments")
  elabElemNu sig omega ctx (App r (NatTy x) []) meta UniverseTy = M.do
    let omega = Elem.instantiateByElaboration omega meta NatTy
    return (Success omega [])
  elabElemNu sig omega ctx tm@(App r (NatTy x) []) meta ty = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
    return (Success omega [ElemElaboration ctx tm meta UniverseTy])
  elabElemNu sig omega ctx (App r (NatTy x) _) meta ty =
    return (Error "ℕ applied to a wrong number of arguments")
  elabElemNu sig omega ctx (App r (ZeroTy x) []) meta UniverseTy = M.do
    let omega = Elem.instantiateByElaboration omega meta ZeroTy
    return (Success omega [])
  elabElemNu sig omega ctx tm@(App r (ZeroTy x) []) meta ty = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
    return (Success omega [ElemElaboration ctx tm meta UniverseTy])
  elabElemNu sig omega ctx (App r (ZeroTy x) _) meta ty =
    return (Error "𝟘 applied to a wrong number of arguments")
  elabElemNu sig omega ctx (App r (OneTy x) []) meta UniverseTy = M.do
    let omega = Elem.instantiateByElaboration omega meta OneTy
    return (Success omega [])
  elabElemNu sig omega ctx tm@(App r (OneTy x) []) meta ty = M.do
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty UniverseTy)
    return (Success omega [ElemElaboration ctx tm meta UniverseTy])
  elabElemNu sig omega ctx (App r (OneTy x) _) meta ty =
    return (Error "𝟙 applied to a wrong number of arguments")
  elabElemNu sig omega ctx (App r (UniverseTy x) []) meta ty =
    return (Error "We don't have 𝕌 : 𝕌!")
  elabElemNu sig omega ctx (App r (UniverseTy x) _) meta ty =
    return (Error "𝕌 applied to a wrong number of arguments")
  elabElemNu sig omega ctx (App r (UnnamedHole r0 Nothing) []) meta ty = M.do
    (omega, n) <- liftUnifyM $ newElemMeta omega ctx ty SolveByUnification
    let omega = Elem.instantiateByElaboration omega meta (OmegaVarElim n Id)
    return (Success omega [])
  elabElemNu sig omega ctx (App r (UnnamedHole r0 (Just vars)) []) meta ty = M.do
    let Just regctxPrefix = pickPrefix (cast ctx) vars
      | Nothing => return (Error "Invalid context prefix")
    let ctxPrefix = cast regctxPrefix
    (omega, n) <- liftUnifyM $ newElemMeta omega ctxPrefix ty SolveByUnification
    let omega = Elem.instantiateByElaboration omega meta (OmegaVarElim n (WkN (length ctx `minus` length regctxPrefix)))
    return (Success omega [])
  elabElemNu sig omega ctx (App r (UnnamedHole x _) _) meta ty =
    return (Error "? applied to arguments not supported")
  elabElemNu sig omega ctx (App r (Hole r0 n Nothing) es) meta ty = M.do
    case (lookup n omega) of
      Just _ => return (Error "Hole already exists: \{n}")
      Nothing => M.do
        omega <- liftUnifyM $ newElemMeta omega ctx n ty NoSolve
        let omega = Elem.instantiateByElaboration omega meta (OmegaVarElim n Id)
        addNamedHole (the Params %search).absFilePath r0 n
        return (Success omega [])
  elabElemNu sig omega ctx (App r (Hole r0 n (Just vars)) es) meta ty = M.do
    case (lookup n omega) of
      Just _ => return (Error "Hole already exists: \{n}")
      Nothing => M.do
        let Just regctxPrefix = pickPrefix (cast ctx) vars
          | Nothing => return (Error "Invalid context prefix")
        let ctxPrefix = cast regctxPrefix
        omega <- liftUnifyM $ newElemMeta omega ctxPrefix n ty SolveByUnification
        let omega = Elem.instantiateByElaboration omega meta (OmegaVarElim n (WkN (length ctx `minus` length regctxPrefix)))
        return (Success omega [])
  elabElemNu sig omega ctx (App r (Unfold r0 x) []) meta ty = M.do
    case lookupLetSignature sig x of
      Just ([<], idx, vRhs, vTy) =>
        return (Success omega [ElemElimElaboration ctx ElEqVal (ElEqTy (SignatureVarElim idx Id) vRhs vTy) [] meta ty])
      Just (sigCtx, idx, vRhs, vTy) =>
        return (Error "Non-empty signature context not supported yet for signature name: \{x}")
      Nothing => return (Error "Undefined signature name: \{x}")
  elabElemNu sig omega ctx (App r (Unfold r0 x) _) meta ty = M.do
    return (Error "!\{x} applied to a wrong number of arguments")
  -- Π-β A (x. B) (x. f) e : (x ↦ f) e ≡ f[e/x] ∈ B[e/x]
  elabElemNu sig omega ctx (App r (PiBeta r0) [(_, Arg ([], dom)), (_, Arg ([x'], cod)), (_, Arg ([x], f)), (_, Arg ([], e))]) meta ty = M.do
    (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
    (omega, f') <- liftUnifyM $ newElemMeta omega (ctx :< (x, OmegaVarElim dom' Id)) (OmegaVarElim cod' Id) SolveByElaboration
    (omega, e') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim dom' Id) SolveByElaboration
    return (Success omega [TypeElaboration ctx dom dom',
                           TypeElaboration (ctx :< (x', OmegaVarElim dom' Id)) cod cod',
                           ElemElaboration (ctx :< (x, OmegaVarElim dom' Id)) f f' (OmegaVarElim cod' Id),
                           ElemElaboration ctx e e' (OmegaVarElim dom' Id),
                           ElemElimElaboration ctx ElEqVal (ElEqTy (PiElim (PiVal x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id) (OmegaVarElim f' Id)) x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id) (OmegaVarElim e' Id)) (OmegaVarElim f' (Ext Id (OmegaVarElim e' Id))) (OmegaVarElim cod' (Ext Id (OmegaVarElim e' Id)))) [] meta ty])
  elabElemNu sig omega ctx (App r (PiBeta r0) _) meta ty =
    return (Error "Π-β applied to a wrong number of arguments")
  -- Π-η f : (x ↦ f x) ≡ f ∈ (x : A) → B
  elabElemNu sig omega ctx (App r (PiEta r0) [(_, Arg ([], f))]) meta ty = M.do
    (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
    (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< ("_", OmegaVarElim dom Id)) SolveByUnification
    (omega, f') <- liftUnifyM $ newElemMeta omega ctx (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)) SolveByElaboration
    return (Success omega [ElemElaboration ctx f f' (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)),
                           ElemElimElaboration ctx ElEqVal (ElEqTy (PiVal "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id) (PiElim (OmegaVarElim f' Wk) "_" (OmegaVarElim dom Wk) (OmegaVarElim cod (Under Wk)) CtxVar)) (OmegaVarElim f' Id) (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))) [] meta ty])
  elabElemNu sig omega ctx (App r (PiEta r0) _) meta ty =
    return (Error "Π-η applied to a wrong number of arguments")
  -- Σ-β₁ A (x. B) a b : (a , b) .π₁ ≡ a ∈ A
  elabElemNu sig omega ctx (App r (SigmaBeta1 r0) [(_, Arg ([], dom)), (_, Arg ([x], cod)), (_, Arg ([], a)), (_, Arg ([], b))]) meta ty = M.do
    (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
    (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim dom' Id) SolveByElaboration
    (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim cod' (Ext Id (OmegaVarElim a' Id))) SolveByElaboration
    return (Success omega [TypeElaboration ctx dom dom',
                           TypeElaboration (ctx :< (x, OmegaVarElim dom' Id)) cod cod',
                           ElemElaboration ctx a a' (OmegaVarElim dom' Id),
                           ElemElaboration ctx b b' (OmegaVarElim cod' (Ext Id (OmegaVarElim a' Id))),
                           ElemElimElaboration ctx ElEqVal (ElEqTy (SigmaElim1 (SigmaVal (OmegaVarElim a' Id) (OmegaVarElim b' Id)) x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id)) (OmegaVarElim a' Id) (OmegaVarElim dom' Id)) [] meta ty])
  elabElemNu sig omega ctx (App r (SigmaBeta1 r0) _) meta ty =
    return (Error "Σ-β₁ applied to a wrong number of arguments")
  -- Σ-β₂ A (x. B) a b : (a , b) .π₂ ≡ b ∈ B(a/x)
  elabElemNu sig omega ctx (App r (SigmaBeta2 r0) [(_, Arg ([], dom)), (_, Arg ([x], cod)), (_, Arg ([], a)), (_, Arg ([], b))]) meta ty = M.do
    (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
    (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim dom' Id) SolveByElaboration
    (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim cod' (Ext Id (OmegaVarElim a' Id))) SolveByElaboration
    return (Success omega [TypeElaboration ctx dom dom',
                           TypeElaboration (ctx :< (x, OmegaVarElim dom' Id)) cod cod',
                           ElemElaboration ctx a a' (OmegaVarElim dom' Id),
                           ElemElaboration ctx b b' (OmegaVarElim cod' (Ext Id (OmegaVarElim a' Id))),
                           ElemElimElaboration ctx ElEqVal (ElEqTy (SigmaElim2 (SigmaVal (OmegaVarElim a' Id) (OmegaVarElim b' Id)) x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id)) (OmegaVarElim b' Id) (OmegaVarElim cod' (Ext Id (OmegaVarElim a' Id)))) [] meta ty])
  elabElemNu sig omega ctx (App r (SigmaBeta2 r0) _) meta ty =
    return (Error "Σ-β₂ applied to a wrong number of arguments")
  -- Σ-η p : (p .π₁ , p .π₂) ≡ p ∈ (x : A) ⨯ B
  elabElemNu sig omega ctx (App r (SigmaEta r0) [(_, Arg ([], p))]) meta ty = M.do
    (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
    (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< ("_", OmegaVarElim dom Id)) SolveByUnification
    (omega, p') <- liftUnifyM $ newElemMeta omega ctx (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)) SolveByElaboration
    return (Success omega [ElemElaboration ctx p p' (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)),
                           ElemElimElaboration ctx ElEqVal (ElEqTy (SigmaVal (SigmaElim1 (OmegaVarElim p' Id) "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)) (SigmaElim2 (OmegaVarElim p' Id) "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))) (OmegaVarElim p' Id) (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))) [] meta ty])
  elabElemNu sig omega ctx (App r (SigmaEta r0) _) meta ty =
    return (Error "Σ-η applied to a wrong number of arguments")
  -- ℕ-β-Z (x. A) z (y. h. s) : ℕ-elim (x. A) z (y. h. s) Z ≡ z ∈ A[Z/x]
  elabElemNu sig omega ctx (App r (NatBetaZ r0) ((_, Arg ([x], schema)) :: (_, Arg ([], z)) :: (_, Arg ([y, h], s)) :: [])) meta ty = M.do
    (omega, schema') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, NatTy)) SolveByElaboration
    (omega, z') <- liftUnifyM $ newElemMeta omega ctx (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)) SolveByElaboration
    (omega, s') <- liftUnifyM $ newElemMeta omega (ctx :< (y, NatTy) :< (h, OmegaVarElim schema' Id))
                                    (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))) SolveByElaboration
    return (Success omega [TypeElaboration (ctx :< (x, NatTy)) schema schema',
                           ElemElaboration ctx z z' (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)),
                           ElemElaboration (ctx :< (y, NatTy) :< (h, OmegaVarElim schema' Id)) s s' (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))),
                           ElemElimElaboration ctx ElEqVal (ElEqTy (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) NatVal0) (OmegaVarElim z' Id) (OmegaVarElim schema' (Ext Id NatVal0))) [] meta ty])
  elabElemNu sig omega ctx (App r (NatBetaZ r0) _) meta ty =
    return (Error "ℕ-β-Z applied to a wrong number of arguments")
  -- ℕ-β-S (x. A) z (y. h. s) t : ℕ-elim (x. A) z (y. h. s) (S t) ≡ s[t/x, ℕ-elim (x. A) z (y. h. s) t/h] ∈ A[S t/x]
  elabElemNu sig omega ctx (App r (NatBetaS r0) [(_, Arg ([x], schema)), (_, Arg ([], z)), (_, Arg ([y, h], s)), (_, Arg ([], t))]) meta ty = M.do
    (omega, schema') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, NatTy)) SolveByElaboration
    (omega, z') <- liftUnifyM $ newElemMeta omega ctx (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)) SolveByElaboration
    (omega, s') <- liftUnifyM $ newElemMeta omega ((ctx :< (y, NatTy)) :< (h, OmegaVarElim schema' Id))
                                    (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))) SolveByElaboration
    (omega, t') <- liftUnifyM $ newElemMeta omega ctx NatTy SolveByElaboration
    return (Success omega [TypeElaboration (ctx :< (x, NatTy)) schema schema',
                           ElemElaboration ctx z z' (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)),
                           ElemElaboration (ctx :< (y, NatTy) :< (h, OmegaVarElim schema' Id)) s s' (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))),
                           ElemElaboration ctx t t' NatTy,
                           ElemElimElaboration ctx ElEqVal (ElEqTy (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) (NatVal1 (OmegaVarElim t' Id))) (OmegaVarElim s' (Ext (Ext Id (OmegaVarElim t' Id)) (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) (OmegaVarElim t' Id)))) (OmegaVarElim schema' (Ext Id (NatVal1 (OmegaVarElim t' Id))))) [] meta ty])
  elabElemNu sig omega ctx (App r (NatBetaS r0) _) meta ty =
    return (Error "ℕ-β-S applied to a wrong number of arguments")
  -- 𝟙⁼ a b : a ≡ b ∈ 𝟙
  elabElemNu sig omega ctx (App r (OneEq r0) [(_, Arg ([], a)), (_, Arg ([], b))]) meta ty = M.do
    (omega, a') <- liftUnifyM $ newElemMeta omega ctx OneTy SolveByElaboration
    (omega, b') <- liftUnifyM $ newElemMeta omega ctx OneTy SolveByElaboration
    return (Success omega [ElemElaboration ctx a a' OneTy,
                           ElemElaboration ctx b b' OneTy,
                           ElemElimElaboration ctx ElEqVal (ElEqTy (OmegaVarElim a' Id)
                                                                 (OmegaVarElim b' Id)
                                                                 OneTy) [] meta ty])
  elabElemNu sig omega ctx (App r (OneEq r0) _) meta ty =
    return (Error "𝟙⁼ applied to a wrong number of arguments")
  -- Π⁼ (x. f) (y. g) (z. p) : (x ↦ f) ≡ (y ↦ g) ∈ (z : A) → B
  elabElemNu sig omega ctx (App r (PiEq r0) [(_, Arg ([x], f)), (_, Arg ([y], g)), (_, Arg ([z], p))]) meta ty = M.do
    (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
    (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< (z, OmegaVarElim dom Id)) SolveByUnification
    (omega, f') <- liftUnifyM $ newElemMeta omega (ctx :< (x, OmegaVarElim dom Id)) (OmegaVarElim cod Id) SolveByElaboration
    (omega, g') <- liftUnifyM $ newElemMeta omega (ctx :< (y, OmegaVarElim dom Id)) (OmegaVarElim cod Id) SolveByElaboration
    (omega, p') <- liftUnifyM $ newElemMeta omega (ctx :< (z, OmegaVarElim dom Id)) (ElEqTy (OmegaVarElim f' Id) (OmegaVarElim g' Id) (OmegaVarElim cod Id)) SolveByElaboration
    return (Success omega [ElemElaboration (ctx :< (x, OmegaVarElim dom Id)) f f' (OmegaVarElim cod Id),
                           ElemElaboration (ctx :< (y, OmegaVarElim dom Id)) g g' (OmegaVarElim cod Id),
                           ElemElaboration (ctx :< (z, OmegaVarElim dom Id)) p p' (ElEqTy (OmegaVarElim f' Id) (OmegaVarElim g' Id) (OmegaVarElim cod Id)),
                           ElemElimElaboration ctx ElEqVal (ElEqTy (PiVal x (OmegaVarElim dom Id) (OmegaVarElim cod Id) (OmegaVarElim f' Id))
                                                               (PiVal y (OmegaVarElim dom Id) (OmegaVarElim cod Id) (OmegaVarElim g' Id))
                                                               (PiTy z (OmegaVarElim dom Id) (OmegaVarElim cod Id))) [] meta ty])
  elabElemNu sig omega ctx (App r (PiEq r0) _) meta ty =
    return (Error "Π⁼ applied to a wrong number of arguments")
  -- Σ⁼ a₀ b₀ a₁ b₁ a b : (a₀ , b₀) ≡ (a₁ , b₁) ∈ (_ : A) ⨯ B
  elabElemNu sig omega ctx (App r (SigmaEq r0) [(_, Arg ([], a0)), (_, Arg ([], b0)), (_, Arg ([], a1)), (_, Arg ([], b1)), (_, Arg ([], a)), (_, Arg ([], b))]) meta ty = M.do
    (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
    (omega, cod) <- liftUnifyM $ newTypeMeta omega (ctx :< ("_", OmegaVarElim dom Id)) SolveByUnification
    (omega, a0') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim dom Id) SolveByElaboration
    (omega, a1') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim dom Id) SolveByElaboration
    (omega, a') <- liftUnifyM $ newElemMeta omega ctx (ElEqTy (OmegaVarElim a0' Id) (OmegaVarElim a1' Id) (OmegaVarElim dom Id)) SolveByElaboration
    (omega, b0') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim cod (Ext Id (OmegaVarElim a0' Id))) SolveByElaboration
    (omega, b1') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim cod (Ext Id (OmegaVarElim a1' Id))) SolveByElaboration
    (omega, b') <- liftUnifyM $ newElemMeta omega ctx (ElEqTy (OmegaVarElim b0' Id) (OmegaVarElim b1' Id) (OmegaVarElim cod (Ext Id (OmegaVarElim a1' Id)))) SolveByElaboration
    return (Success omega [ElemElaboration ctx a0 a0' (OmegaVarElim dom Id),
                           ElemElaboration ctx a1 a1' (OmegaVarElim dom Id),
                           ElemElaboration ctx a a' (ElEqTy (OmegaVarElim a0' Id) (OmegaVarElim a1' Id) (OmegaVarElim dom Id)),
                           ElemElaboration ctx b0 b0' (OmegaVarElim cod (Ext Id (OmegaVarElim a0' Id))),
                           ElemElaboration ctx b1 b1' (OmegaVarElim cod (Ext Id (OmegaVarElim a1' Id))),
                           ElemElaboration ctx b b' (ElEqTy (OmegaVarElim b0' Id) (OmegaVarElim b1' Id) (OmegaVarElim cod (Ext Id (OmegaVarElim a1' Id)))),
                           ElemElimElaboration ctx ElEqVal (ElEqTy (SigmaVal (OmegaVarElim a0' Id) (OmegaVarElim b0' Id))
                                                                 (SigmaVal (OmegaVarElim a1' Id) (OmegaVarElim b1' Id))
                                                                 (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))) [] meta ty])
  elabElemNu sig omega ctx (App r (SigmaEq r0) _) meta ty =
    return (Error "Σ⁼ applied to a wrong number of arguments")
  elabElemNu sig omega ctx (App r (Tm _ tm) []) meta ty = M.do
    return (Success omega [ElemElaboration ctx tm meta ty])
  elabElemNu sig omega ctx (App r (Tm _ tm) (_ :: _)) meta ty = M.do
    return (Error "Do we want to elaborate this case? There might be ambiguity in implicit resolution because we might not know the type of the head?")
    {- (omega, t) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
    (omega, tm') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t Id) SolveByElaboration
    return (Success omega [ElemElaboration ctx tm tm' (OmegaVarElim t Id),
                           ElemElimElaboration ctx (OmegaVarElim tm' Id) (OmegaVarElim t Id) es meta ty]) -}
  -- Ξ Ω ⊦ ∀x ∈ Ω (x ∉ FV(Γ))
  -- Ξ Ω Γ ⊦ ∀x ∈ Ω (x ∉ FV(A))
  -- Given a correct tactic, success of elaborating it depends on context Γ and type A.
  -- To make sure that we can approach tactics in the source in any order, we need to make sure the context and type of the tactic
  -- in question can't be refined any further over time. Or in other words, they both must not contain free Ω variables.
  --
  -- Ξ Ω ⊦ ⟦α⟧ ⇝ α' : ε ⇒ ε (Γ ⊦ A)
  -- Ξ Ω Γ ⊦ ⟦tac α⟧ ⇝ α' · : A
  elabElemNu sig omega ctx (Tac r alpha) meta ty = M.do
    free <- Elab.liftM $ freeOmegaName sig omega ctx
    let True = isEmpty free
      | False => return (Stuck "Context contains free Ω variables: \{show (List.inorder free)}")
    free <- Elab.liftM $ freeOmegaName sig omega ty
    let True = isEmpty free
      | False => return (Stuck "Type contains free Ω variables: \{show (List.inorder free)}")
    Right (omega, [<], interp) <- elabTactic sig omega alpha [< ("_", ElemEntry ctx ty)]
      | Left err => return (Error err)
      | Right (_, interp) => return (Error "Source signature of the tactic must be ε, but it is not.")
    let [< ElemEntryInstance solution] = interp [<]
      | _ => throw "elabElemNu(Tac)"
    let omega = instantiateByElaboration omega meta solution
    return (Success omega [])
  elabElemNu sig omega ctx (App r (Underscore r0) _) meta ty =
    return (Error "_ is not a valid term")
  elabElemNu sig omega ctx (App r (Box r0) _) meta ty =
    return (Error "☐ is not a valid term")
  elabElemNu sig omega ctx (App r (El r0) _) meta ty = M.do
    return (Error "El _ is not an element")

  ||| Σ Ω Γ ⊦ ⟦t⟧ ⇝ p : A
  public export
  elabElem : Params
          => Signature
          -> Omega
          -> Context
          -> SurfaceTerm
          -> OmegaName
          -> CoreTyp
          -> ElabM Elaboration.Result
  elabElem sig omega ctx tm p ty = elabElemNu sig omega ctx tm p !(Elab.liftM $ openEval sig omega ty)

  ||| Σ Ω Γ ⊦ ⟦A⟧ ⇝ A' type
  ||| Here we implicitly insert El to convert from 𝕌 to type
  public export
  elabType : Params
          => Signature
          -> Omega
          -> Context
          -> SurfaceTerm
          -> OmegaName
          -> ElabM Elaboration.Result
  elabType sig omega ctx (PiTy r x dom cod) meta = M.do
    (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
    let omega = Typ.instantiateByElaboration omega meta (PiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
    return (Success omega [TypeElaboration ctx dom dom', TypeElaboration (ctx :< (x, OmegaVarElim dom' Id)) cod cod'])
  elabType sig omega ctx (ImplicitPiTy r x dom cod) meta = M.do
    (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
    let omega = Typ.instantiateByElaboration omega meta (ImplicitPiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
    return (Success omega [TypeElaboration ctx dom dom', TypeElaboration (ctx :< (x, OmegaVarElim dom' Id)) cod cod'])
  elabType sig omega ctx (SigmaTy r x dom cod) meta = M.do
    (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    (omega, cod') <- liftUnifyM $ newTypeMeta omega (ctx :< (x, OmegaVarElim dom' Id)) SolveByElaboration
    let omega = Typ.instantiateByElaboration omega meta (SigmaTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
    return (Success omega [TypeElaboration ctx dom dom', TypeElaboration (ctx :< (x, OmegaVarElim dom' Id)) cod cod'])
  elabType sig omega ctx (FunTy r dom cod) meta = M.do
    (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    (omega, cod') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    let omega = Typ.instantiateByElaboration omega meta (PiTy "_" (OmegaVarElim dom' Id) (OmegaVarElim cod' Wk))
    return (Success omega [TypeElaboration ctx dom dom', TypeElaboration ctx cod cod'])
  elabType sig omega ctx (ProdTy r dom cod) meta = M.do
    (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    (omega, cod') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    let omega = Typ.instantiateByElaboration omega meta (SigmaTy "_" (OmegaVarElim dom' Id) (OmegaVarElim cod' Wk))
    return (Success omega [TypeElaboration ctx dom dom', TypeElaboration ctx cod cod'])
  elabType sig omega ctx (TyEqTy r a b) meta = M.do
    (omega, a') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    (omega, b') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    let omega = Typ.instantiateByElaboration omega meta (TyEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id))
    return (Success omega [ TypeElaboration ctx a a',
                            TypeElaboration ctx b b'
                          ]
           )
  elabType sig omega ctx (ElEqTy r a b t) meta = M.do
    (omega, t') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
    (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
    (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
    let omega = Typ.instantiateByElaboration omega meta (ElEqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) (OmegaVarElim t' Id))
    return (Success omega [TypeElaboration ctx t t',
                           ElemElaboration ctx a a' (OmegaVarElim t' Id),
                           ElemElaboration ctx b b' (OmegaVarElim t' Id)
                          ]
           )
  elabType sig omega ctx (PiVal r x f) meta =
    return (Error "_ ↦ _ is not a type")
  elabType sig omega ctx (ImplicitPiVal r x f) meta =
    return (Error "{_} ↦ _ is not a type")
  elabType sig omega ctx (SigmaVal r a b) meta =
    return (Error "(_, _) is not a type")
  elabType sig omega ctx tm@(App r (Var r0 x) es) meta = M.do
    (omega, t') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    let omega = Typ.instantiateByElaboration omega meta (El (OmegaVarElim t' Id))
    return (Success omega [ElemElaboration ctx tm t' UniverseTy])
  elabType sig omega ctx (App r (OneVal x) _) meta = M.do
    return (Error "() is not a type")
  elabType sig omega ctx (App r (NatVal0 x) _) meta = M.do
    return (Error "Z is not a type")
  elabType sig omega ctx (App r (NatVal1 _) _) meta = M.do
    return (Error "S is not a type")
  elabType sig omega ctx tm@(App r (NatElim _) _) meta = M.do
    (omega, t') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    let omega = Typ.instantiateByElaboration omega meta (El (OmegaVarElim t' Id))
    return (Success omega [ElemElaboration ctx tm t' UniverseTy])
  elabType sig omega ctx tm@(App r (ZeroElim _) _) meta = M.do
    (omega, t') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    let omega = Typ.instantiateByElaboration omega meta (El (OmegaVarElim t' Id))
    return (Success omega [ElemElaboration ctx tm t' UniverseTy])
  elabType sig omega ctx (App _ (EqElim _) _) meta = M.do
    return (Error "J is not a type")
  elabType sig omega ctx (App r (EqVal x) _) meta = M.do
    return (Error "Refl is not a type")
  elabType sig omega ctx (App r (NatTy x) []) meta = M.do
    let omega = Typ.instantiateByElaboration omega meta NatTy
    return (Success omega [])
  elabType sig omega ctx (App r (NatTy x) _) meta =
    return (Error "ℕ applied to a wrong number of arguments")
  elabType sig omega ctx (App r (ZeroTy x) []) meta = M.do
    let omega = Typ.instantiateByElaboration omega meta ZeroTy
    return (Success omega [])
  elabType sig omega ctx (App r (ZeroTy x) _) meta =
    return (Error "𝟘 applied to a wrong number of arguments")
  elabType sig omega ctx (App r (OneTy x) []) meta = M.do
    let omega = Typ.instantiateByElaboration omega meta OneTy
    return (Success omega [])
  elabType sig omega ctx (App r (OneTy x) _) meta =
    return (Error "𝟙 applied to a wrong number of arguments")
  elabType sig omega ctx (App r (UniverseTy x) []) meta = M.do
    let omega = Typ.instantiateByElaboration omega meta UniverseTy
    return (Success omega [])
  elabType sig omega ctx (App r (UniverseTy x) _) meta =
    return (Error "𝕌 applied to a wrong number of arguments")
  elabType sig omega ctx (App r (UnnamedHole r0 Nothing) []) meta = M.do
    (omega, n) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
    let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim n Id)
    return (Success omega [])
  elabType sig omega ctx (App r (UnnamedHole r0 (Just vars)) []) meta = M.do
    let Just regctxPrefix = pickPrefix (cast ctx) vars
      | Nothing => return (Error "Invalid context prefix")
    let ctxPrefix = cast regctxPrefix
    (omega, n) <- liftUnifyM $ newTypeMeta omega ctxPrefix SolveByUnification
    let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim n (WkN (length ctx `minus` length regctxPrefix)))
    return (Success omega [])
  elabType sig omega ctx (App r (UnnamedHole x vars) _) meta =
    return (Error "? applied to arguments not supported")
  elabType sig omega ctx (App r (Hole r0 n Nothing) es) meta =
    case (lookup n omega) of
      Just _ => return (Error "Hole already exists: \{n}")
      Nothing => M.do
        omega <- liftUnifyM $ newTypeMeta omega ctx n NoSolve
        let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim n Id)
        addNamedHole (the Params %search).absFilePath r0 n
        return (Success omega [])
  elabType sig omega ctx (App r (Hole r0 n (Just vars)) es) meta =
    case (lookup n omega) of
      Just _ => return (Error "Hole already exists: \{n}")
      Nothing => M.do
        let Just regctxPrefix = pickPrefix (cast ctx) vars
          | Nothing => return (Error "Invalid context prefix")
        let ctxPrefix = cast regctxPrefix
        omega <- liftUnifyM $ newTypeMeta omega ctxPrefix n SolveByUnification
        let omega = Typ.instantiateByElaboration omega meta (OmegaVarElim n (WkN (length ctx `minus` length regctxPrefix)))
        return (Success omega [])
  elabType sig omega ctx (App r (Unfold r0 x) _) meta = M.do
    return (Error "! is not a type")
  elabType sig omega ctx tm@(App r (PiBeta r0) _) meta = M.do
    return (Error "Π-β is not a type")
  elabType sig omega ctx tm@(App r (SigmaBeta1 r0) _) meta = M.do
    return (Error "Σ-β₁ is not a type")
  elabType sig omega ctx tm@(App r (SigmaBeta2 r0) _) meta = M.do
    return (Error "Σ-β₂ is not a type")
  elabType sig omega ctx (App r (PiEta r0) _) meta = M.do
    return (Error "Π-η is not a type")
  elabType sig omega ctx (App r (SigmaEta r0) _) meta = M.do
    return (Error "Σ-η is not a type")
  elabType sig omega ctx (App r (NatBetaZ r0) _) meta = M.do
    return (Error "ℕ-β-Z is not a type")
  elabType sig omega ctx (App r (NatBetaS r0) _) meta = M.do
    return (Error "ℕ-β-S is not a type")
  elabType sig omega ctx (App r (PiEq r0) _) meta = M.do
    return (Error "Π⁼ is not a type")
  elabType sig omega ctx (App r (SigmaEq r0) _) meta = M.do
    return (Error "Σ⁼ is not a type")
  elabType sig omega ctx (App r (OneEq r0) _) meta = M.do
    return (Error "𝟙⁼ is not a type")
  elabType sig omega ctx (App r (Tm _ tm) []) meta = M.do
    return (Success omega [TypeElaboration ctx tm meta])
  elabType sig omega ctx (App r (Tm _ tm) es) meta = M.do
    return (Error "_ _ is not a type")
  elabType sig omega ctx (Tac r alpha) meta = M.do
    return (Error "tac is not supported in a type yet")
  elabType sig omega ctx (App r (Underscore r0) _) meta =
    return (Error "_ is not a valid term")
  elabType sig omega ctx (App r (Box r0) _) meta =
    return (Error "☐ is not a valid term")
  elabType sig omega ctx (App r (El r0) [(_, Arg ([], el))]) meta = M.do
    -- ⟦e⟧ : 𝕌
    -- -------------------
    -- ⟦El e⟧ ⇝ El e' type
    (omega, el') <- liftUnifyM $ newElemMeta omega ctx UniverseTy SolveByElaboration
    let omega = Typ.instantiateByElaboration omega meta (El (OmegaVarElim el' Id))
    return (Success omega [ElemElaboration ctx el el' UniverseTy])
  elabType sig omega ctx (App r (El r0) _) meta = M.do
    return (Error "El applied to a wrong number of arguments")

  namespace Typ
    ||| Try applying rewrite tactic on a well-formed type
    ||| Γ ⊦ T type
    ||| The term must be head-neutral w.r.t. open evaluation
    ||| OpFreeTerm must represent a valid path!
    ||| See Surface/Language for a description of being a valid path.
    public export
    applyRewriteNu : Params => Signature -> Omega -> Context -> Typ -> OpFreeTerm -> SurfaceTerm -> Bool -> ElabM (Either Range (Omega, Typ))
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
    applyRewriteNu sig omega gamma (PiTy x dom cod) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (ImplicitPiTy x dom cod) (ImplicitPiTy r _ pdom (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, dom) <- applyRewrite sig omega gamma dom pdom prf direct
      return (omega, ImplicitPiTy x dom cod)
    applyRewriteNu sig omega gamma (ImplicitPiTy x dom cod) (ImplicitPiTy r _ (App _ (Underscore _) []) pcod) prf direct = MEither.do
      (omega, cod) <- applyRewrite sig omega (gamma :< (x, dom)) cod pcod prf direct
      return (omega, ImplicitPiTy x dom cod)
    applyRewriteNu sig omega gamma (ImplicitPiTy x dom cod) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (SigmaTy x dom cod) (SigmaTy r _ pdom (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, dom) <- applyRewrite sig omega gamma dom pdom prf direct
      return (omega, SigmaTy x dom cod)
    applyRewriteNu sig omega gamma (SigmaTy x dom cod) (SigmaTy r _ (App _ (Underscore _) []) pcod) prf direct = MEither.do
      (omega, cod) <- applyRewrite sig omega (gamma :< (x, dom)) cod pcod prf direct
      return (omega, SigmaTy x dom cod)
    applyRewriteNu sig omega gamma (SigmaTy x dom cod) p prf direct = error (range p)
    -- We need to figure out how to support this.
    -- Note that the endpoint is a type!
    -- This won't work:
    --             vvv e is a type! This is ill-typed!
    -- Γ ⊦ p : e₀ ≡ e ∈ 𝕌
    -- ⟦Γ | e | ☐ | p, True⟧ = e₀
    applyRewriteNu sig omega gamma e (App r (Box _) []) prf b = MEither.do
      error r
    applyRewriteNu sig omega gamma NatTy p prf direct = error (range p)
    applyRewriteNu sig omega gamma ZeroTy p prf direct = error (range p)
    applyRewriteNu sig omega gamma OneTy p prf direct = error (range p)
    applyRewriteNu sig omega gamma UniverseTy p prf direct = error (range p)
    applyRewriteNu sig omega gamma (ContextSubstElim x y) f prf direct = assert_total $ idris_crash "applyRewriteNu(_[_])"
    applyRewriteNu sig omega gamma (SignatureSubstElim x y) f prf direct = assert_total $ idris_crash "applyRewriteNu(_[_])"
    applyRewriteNu sig omega gamma (OmegaVarElim str x) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (TyEqTy a b) (TyEqTy _ pa (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, a) <- applyRewrite sig omega gamma a pa prf direct
      return (omega, TyEqTy a b)
    applyRewriteNu sig omega gamma (TyEqTy a b) (TyEqTy _ (App _ (Underscore _) []) pb) prf direct = MEither.do
      (omega, b) <- applyRewrite sig omega gamma b pb prf direct
      return (omega, TyEqTy a b)
    applyRewriteNu sig omega gamma (TyEqTy a b) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ pa (App _ (Underscore _) []) (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, a) <- applyRewrite sig omega gamma a pa prf direct
      return (omega, ElEqTy a b ty)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ (App _ (Underscore _) []) pb (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, b) <- applyRewrite sig omega gamma b pb prf direct
      return (omega, ElEqTy a b ty)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ (App _ (Underscore _) []) (App _ (Underscore _) []) pty) prf direct = MEither.do
      (omega, ty) <- applyRewrite sig omega gamma ty pty prf direct
      return (omega, ElEqTy a b ty)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) p prf direct = error (range p)

    public export
    applyRewrite : Params => Signature -> Omega -> Context -> Typ -> OpFreeTerm -> SurfaceTerm -> Bool -> ElabM (Either Range (Omega, Typ))
    applyRewrite sig omega gamma t p prf direct = MEither.do
      applyRewriteNu sig omega gamma !(ElabEither.liftM $ openEval sig omega t) p prf direct

  namespace Elem
    ||| Try applying rewrite tactic on a well-typed element
    ||| Γ ⊦ t : T
    ||| The element must be head-neutral w.r.t. open evaluation
    ||| OpFreeTerm must represent a valid path!
    ||| See Surface/Language for a description of being a valid path.
    public export
    applyRewriteNu : Params => Signature -> Omega -> Context -> Elem -> OpFreeTerm -> SurfaceTerm -> Bool -> ElabM (Either Range (Omega, Elem))
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
    applyRewriteNu sig omega gamma (PiTy x dom cod) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (ImplicitPiTy x dom cod) (ImplicitPiTy r _ pdom (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, dom) <- applyRewrite sig omega gamma dom pdom prf direct
      return (omega, ImplicitPiTy x dom cod)
    applyRewriteNu sig omega gamma (ImplicitPiTy x dom cod) (ImplicitPiTy r _ (App _ (Underscore _) []) pcod) prf direct = MEither.do
      (omega, cod) <- applyRewrite sig omega (gamma :< (x, El dom)) cod pcod prf direct
      return (omega, ImplicitPiTy x dom cod)
    applyRewriteNu sig omega gamma (ImplicitPiTy x dom cod) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (SigmaTy x dom cod) (SigmaTy r _ pdom (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, dom) <- applyRewrite sig omega gamma dom pdom prf direct
      return (omega, SigmaTy x dom cod)
    applyRewriteNu sig omega gamma (SigmaTy x dom cod) (SigmaTy r _ (App _ (Underscore _) []) pcod) prf direct = MEither.do
      (omega, cod) <- applyRewrite sig omega (gamma :< (x, El dom)) cod pcod prf direct
      return (omega, SigmaTy x dom cod)
    applyRewriteNu sig omega gamma (SigmaTy x dom cod) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (PiVal x a b body) (PiVal r _ pbody) prf direct = MEither.do
      (omega, body) <- applyRewrite sig omega (gamma :< (x, a)) body pbody prf direct
      return (omega, PiVal x a b body)
    applyRewriteNu sig omega gamma (PiVal x a b body) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (ImplicitPiVal x a b body) (ImplicitPiVal r _ pbody) prf direct = MEither.do
      (omega, body) <- applyRewrite sig omega (gamma :< (x, a)) body pbody prf direct
      return (omega, ImplicitPiVal x a b body)
    applyRewriteNu sig omega gamma (ImplicitPiVal x a b body) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (SigmaVal a b) (SigmaVal r pa (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, a) <- applyRewrite sig omega gamma a pa prf direct
      return (omega, SigmaVal a b)
    applyRewriteNu sig omega gamma (SigmaVal a b) (SigmaVal r (App _ (Underscore _) []) pb) prf direct = MEither.do
      (omega, b) <- applyRewrite sig omega gamma b pb prf direct
      return (omega, SigmaVal a b)
    applyRewriteNu sig omega gamma (SigmaVal a b) p prf direct = error (range p)
    -- Γ ⊦ p : e₀ ≡ e ∈ A
    -- ⟦Γ | e | ☐ | p, True⟧ = e₀
    applyRewriteNu sig omega gamma e (App r (Box _) []) prf True = MEither.do
      (omega, ty') <- liftUnifyM' $ newTypeMeta omega gamma SolveByUnification
      (omega, e0') <- liftUnifyM' $ newElemMeta omega gamma (OmegaVarElim ty' Id) SolveByUnification
      (omega, prf') <- liftUnifyM' $ newElemMeta omega gamma (ElEqTy (OmegaVarElim e0' Id) e (OmegaVarElim ty' Id)) SolveByElaboration
      case !(mapResult Right (Elaboration.solve sig omega [ElemElaboration gamma prf prf' (ElEqTy (OmegaVarElim e0' Id) e (OmegaVarElim ty' Id))])) of
        Success omega => MEither.do
          return (omega, OmegaVarElim e0' Id)
                    --FIX:
        Stuck omega [] [] =>
          case (containsNamedHolesOnly omega) of
            True => MEither.do
              return (omega, OmegaVarElim e0' Id)
            False => error r
        Stuck omega elabs cons => error r
        Error {} => error r
    -- Γ ⊦ p : e ≡ e₀ ∈ A
    -- ⟦Γ | e | ☐ | p, False⟧ = e₀
    applyRewriteNu sig omega gamma e (App r (Box _) []) prf False = MEither.do
      (omega, ty') <- liftUnifyM' $ newTypeMeta omega gamma SolveByUnification
      (omega, e0') <- liftUnifyM' $ newElemMeta omega gamma (OmegaVarElim ty' Id) SolveByUnification
      (omega, prf') <- liftUnifyM' $ newElemMeta omega gamma (ElEqTy e (OmegaVarElim e0' Id) (OmegaVarElim ty' Id)) SolveByElaboration
      case !(mapResult Right (Elaboration.solve sig omega [ElemElaboration gamma prf prf' (ElEqTy e (OmegaVarElim e0' Id) (OmegaVarElim ty' Id))])) of
        Success omega => MEither.do
          return (omega, OmegaVarElim e0' Id)
                    --FIX:
        Stuck omega [] [] =>
          case (containsNamedHolesOnly omega) of
            True => MEither.do
              return (omega, OmegaVarElim e0' Id)
            False => MEither.do
              write "rewrite⁻¹: elaboration stuck, unsolved metas" <&> Right
              error r
        Stuck omega elabs cons => MEither.do
          write "rewrite⁻¹: elaboration stuck, unsolved elabs and cons" <&> Right
          error r
        Error omega (Left err) => MEither.do
          let err = ElaborationError omega err
          write "rewrite⁻¹ failed at ☐:" <&> Right
          write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right
          error r
        Error omega (Right err) => MEither.do
          let err = UnificationError omega err
          write "rewrite⁻¹ failed at ☐:" <&> Right
          write (renderDocTerm !(ElabEither.liftM $ pretty sig err)) <&> Right
          error r
    applyRewriteNu sig omega gamma (PiElim f x a b e) (App r h es) prf direct = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error r
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          (omega, f) <- applyRewrite sig omega gamma f (App r h (cast es)) prf direct
          return (omega, PiElim f x a b e)
        (es :< (_, Arg ([], pe))) => MEither.do
          (omega, e) <- applyRewrite sig omega gamma e pe prf direct
          return (omega, PiElim f x a b e)
        (es :< (r, _)) => MEither.do
          error r
    applyRewriteNu sig omega gamma (PiElim f x a b e) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (ImplicitPiElim f x a b e) (App r h es) prf direct = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error r
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          (omega, f) <- applyRewrite sig omega gamma f (App r h (cast es)) prf direct
          return (omega, PiElim f x a b e)
        (es :< (_, Arg ([], pe))) => MEither.do
          (omega, e) <- applyRewrite sig omega gamma e pe prf direct
          return (omega, PiElim f x a b e)
        (es :< (r, _)) => MEither.do
          error r
    applyRewriteNu sig omega gamma (ImplicitPiElim f x a b e) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (SigmaElim1 f x a b) (App r h es) prf direct = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error r
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          (omega, f) <- applyRewrite sig omega gamma f (App r h (cast es)) prf direct
          return (omega, SigmaElim1 f x a b)
        (es :< (_, Pi1)) => MEither.do
          (omega, f) <- applyRewrite sig omega gamma f (App r h (cast es)) prf direct
          return (omega, SigmaElim1 f x a b)
        (es :< (r, _)) => MEither.do
          error r
    applyRewriteNu sig omega gamma (SigmaElim1 f x a b) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (SigmaElim2 f x a b) (App r h es) prf direct = MEither.do
      let es' = cast {to = SnocList (Range, OpFreeElimEntry)} es
      case es' of
        [<] => error r
        (es :< (_, Arg ([], App _ (Underscore _) []))) => MEither.do
          (omega, f) <- applyRewrite sig omega gamma f (App r h (cast es)) prf direct
          return (omega, SigmaElim2 f x a b)
        (es :< (_, Pi2)) => MEither.do
          (omega, f) <- applyRewrite sig omega gamma f (App r h (cast es)) prf direct
          return (omega, SigmaElim2 f x a b)
        (es :< (r, _)) => MEither.do
          error r
    applyRewriteNu sig omega gamma (SigmaElim2 f x a b) p prf direct = error (range p)
    applyRewriteNu sig omega gamma NatVal0 p prf direct = error (range p)
    applyRewriteNu sig omega gamma (NatVal1 t) (App r (NatVal1 _) [(_, Arg ([], p))]) prf direct = MEither.do
      (omega, t) <- applyRewrite sig omega gamma t p prf direct
      return (omega, NatVal1 t)
    applyRewriteNu sig omega gamma (NatVal1 t) p prf direct = error (range p)
    applyRewriteNu sig omega gamma NatTy p prf direct = error (range p)
    applyRewriteNu sig omega gamma ZeroTy p prf direct = error (range p)
    applyRewriteNu sig omega gamma OneTy p prf direct = error (range p)
    applyRewriteNu sig omega gamma OneVal p prf direct = error (range p)
    applyRewriteNu sig omega gamma (ZeroElim t) (App r (ZeroElim _)
                                                       [(_, Arg ([], pt))]
                                                ) prf direct = MEither.do
      (omega, t) <- applyRewrite sig omega gamma t pt prf direct
      return (omega, ZeroElim t)
    applyRewriteNu sig omega gamma (ZeroElim t) p prf direct = error (range p)
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
        _ => error r
    applyRewriteNu sig omega gamma (NatElim x schema z y h s t) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (ContextSubstElim x y) f prf direct = assert_total $ idris_crash "applyRewriteNu(_[_])"
    applyRewriteNu sig omega gamma (SignatureSubstElim x y) f prf direct = assert_total $ idris_crash "applyRewriteNu(_[_])"
    applyRewriteNu sig omega gamma (ContextVarElim k) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (SignatureVarElim k sigma) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (OmegaVarElim str x) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (TyEqTy a b) (TyEqTy _ pa (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, a) <- applyRewrite sig omega gamma a pa prf direct
      return (omega, TyEqTy a b)
    applyRewriteNu sig omega gamma (TyEqTy a b) (TyEqTy _ (App _ (Underscore _) []) pb) prf direct = MEither.do
      (omega, b) <- applyRewrite sig omega gamma b pb prf direct
      return (omega, TyEqTy a b)
    applyRewriteNu sig omega gamma (TyEqTy a b) p prf direct = error (range p)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ pa (App _ (Underscore _) []) (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, a) <- applyRewrite sig omega gamma a pa prf direct
      return (omega, ElEqTy a b ty)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ (App _ (Underscore _) []) pb (App _ (Underscore _) [])) prf direct = MEither.do
      (omega, b) <- applyRewrite sig omega gamma b pb prf direct
      return (omega, ElEqTy a b ty)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) (ElEqTy _ (App _ (Underscore _) []) (App _ (Underscore _) []) pty) prf direct = MEither.do
      (omega, ty) <- applyRewrite sig omega gamma ty pty prf direct
      return (omega, ElEqTy a b ty)
    applyRewriteNu sig omega gamma (ElEqTy a b ty) p prf direct = error (range p)
    applyRewriteNu sig omega gamma TyEqVal p prf direct = error (range p)
    applyRewriteNu sig omega gamma ElEqVal p prf direct = error (range p)

    public export
    applyRewrite : Params => Signature -> Omega -> Context -> Elem -> OpFreeTerm -> SurfaceTerm -> Bool -> ElabM (Either Range (Omega, Elem))
    applyRewrite sig omega gamma t p prf direct = MEither.do
      applyRewriteNu sig omega gamma !(ElabEither.liftM $ openEval sig omega t) p prf direct

  ||| Ξ Ω ⊦ ⟦α⟧ ⇝ α' : Σ₁ ⇒ Σ₀
  public export
  elabTactic : Params
            => Signature
            -> Omega
            -> OpFreeTactic
            -> (target : Signature)
            -> ElabM (Either String (Omega, Signature, SignatureInst -> SignatureInst))
  elabTactic sig omega (Id r) target = M.do
    write (renderDocTerm !(Elab.liftM $ prettySignature sig omega target))
    return (Right (omega, target, id))
  elabTactic sig omega (Trivial r) [< (x, ElemEntry ctx ty)] = M.do
    case !(Elab.liftM $ applyTrivial sig omega ty) of
      Just done => return (Right (omega, [<], \_ => [< ElemEntryInstance done]))
      Nothing => return (Left "Can't apply 'trivial'")
  elabTactic sig omega (Trivial r) _ = M.do
    return (Left "Wrong signature for tactic: 'trivial'")
  elabTactic sig omega (Composition r (alpha ::: [])) target = M.do
    elabTactic sig omega alpha target
  elabTactic sig omega (Composition r (alpha ::: beta :: gammas)) target = M.do
    Right (omega, alphaSource, alphaInterp) <- elabTactic sig omega alpha target
      | Left err => return (Left err)
    Right (omega, source, restInterp) <- elabTactic sig omega (Composition r (beta ::: gammas)) alphaSource
      | Left err => return (Left err)
    return (Right (omega, source, restInterp . alphaInterp))
  -- ⟦reduce ρ⟧ : ε (Γ ⊦ B) ⇒ ε (Γ ⊦ A)
  elabTactic sig omega (Reduce r path) [< (x, ElemEntry ctx ty)] = M.do
   Right ty' <- Elab.liftM $ applyReduce sig omega ty path
     | Left r => --FIX: use the range
                 return (Left "Can't apply 'reduce', range: \{show r}, ρ: \{show path}")
   return (Right (omega, [< (x, ElemEntry ctx ty')], id))
  elabTactic sig omega (Reduce r path) _ = return (Left "Target context is empty or its last entry is a let")
  elabTactic sig omega (RewriteInv r path prf) [< (x, ElemEntry ctx ty)] = M.do
    case !(applyRewrite sig omega ctx ty path prf False) of
      Left r0 => M.do
        write "Rewrite⁻¹ failed at \{show r0}"
        return (Left "rewrite⁻¹ failed at \{show r0}")
      Right (omega, ty0) => return (Right (omega, [< (x, ElemEntry ctx ty0)], id))
  elabTactic sig omega (RewriteInv r path prf) target = MEither.do
    error "Wrong context for rewrite⁻¹"
  elabTactic sig omega (Rewrite r path prf) [< (x, ElemEntry ctx ty)] = M.do
    case !(applyRewrite sig omega ctx ty path prf True) of
      Left r0 => M.do
        write "Rewrite failed at \{show r0}"
        return (Left "rewrite failed at \{show r0}")
      Right (omega, ty0) => return (Right (omega, [< (x, ElemEntry ctx ty0)], id))
  elabTactic sig omega (Rewrite r path prf) target = MEither.do
    error "Wrong context for rewrite"
  elabTactic sig omega (Exact r tm) [< (x, ElemEntry ctx ty)] = M.do
    (omega, m') <- liftUnifyM $ newElemMeta omega ctx ty SolveByElaboration
    case !(Elaboration.solve sig omega [ElemElaboration ctx tm m' ty]) of
      Success omega => return (Right (omega, [<], \_ => [< ElemEntryInstance (OmegaVarElim m' Id)]))
                  --FIX:
      Stuck omega [] [] =>
        case (containsNamedHolesOnly omega) of
          True => return (Right (omega, [<], \_ => [< ElemEntryInstance (OmegaVarElim m' Id)]))
          False => return (Left "Stuck elaborating exact term; have some unsolved holes: \{renderDocNoAnn !(Elab.liftM $ prettyOmega sig omega)}" )
      Stuck omega elabs cons => M.do
        let err = Stuck omega elabs cons
        return (Left "Stuck elaborating the exact term;\n \{renderDocNoAnn !(liftM $ pretty sig err)}")
      Error {} => return (Left "Error elaborating the exact term")
  elabTactic sig omega (Exact r tm) target = return (Left "Wrong target context for exact tactic")
  elabTactic sig omega (Split r [<] alpha) target =
    elabTactic sig omega alpha target
  -- THOUGHT: Pretty sure Split can be generalised such that the source context is arbitrary
  -- ⟦α⟧ ⇝ α' : ε ⇒ Σ
  -- ⟦β⟧ ⇝ β' : ε ⇒ (Γ(id, α' ·) ⊦ A(id, α' ·))
  -- --------------------------
  -- ⟦* α * β⟧ ⇝ \x => α' x, β' x : ε ⇒ Σ (Γ ⊦ A)
  elabTactic sig omega (Split r (betas :< beta) alpha) (sigma :< (x, ElemEntry ctx ty)) = M.do
    Right (omega, [<], interpA) <- elabTactic sig omega (Split r betas beta) sigma
      | _ => return (Left "Error elaborating Split")
    Right (omega, [<], interpB) <- elabTactic sig omega alpha [< (x, ElemEntry (subst ctx (ext Id (cast (interpA [<])))) (SignatureSubstElim ty (ext Id (cast (interpA [<])))))]
      | _ => return (Left "Error elaborating Split")
    return (Right (omega, [<], \x => interpA x ++ interpB x))
  elabTactic sig omega (Split r (betas :< beta) alpha) target = return (Left "Wrong target context for split tactic")
  elabTactic sig omega (Let r x e) target =  M.do
    (omega, ty') <- liftUnifyM $ newTypeMeta omega [<] SolveByUnification
    let ty = OmegaVarElim ty' Id
    (omega, e') <- liftUnifyM $ newElemMeta omega [<] ty SolveByElaboration
    -- Σ (x ≔ t : A)
    let source = target :< (x, LetElemEntry [<] (OmegaVarElim e' Id) ty)
    let
      f : SignatureInst -> SignatureInst
      f [<] = assert_total $ idris_crash "elabTactic/let"
      f (ts :< t) = ts
    case !(Elaboration.solve sig omega [ElemElaboration [<] e e' ty]) of
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

  ||| Σ Ω Γ ⊦ (t : T) ⟦ē⟧ ⇝ t' : A
  ||| Where T is head-neutral w.r.t. open evaluation.
  public export
  elabElemElimNu : Params
                => Signature
                -> Omega
                -> Context
                -> CoreElem
                -> CoreTyp
                -> OpFreeElim
                -> OmegaName
                -> CoreTyp
                -> ElabM Elaboration.Result
  elabElemElimNu sig omega ctx head (ImplicitPiTy x dom cod) ((_, ImplicitArg e) :: es) meta ty = M.do
    (omega, e') <- liftUnifyM $ newElemMeta omega ctx dom SolveByElaboration
    return (Success omega [ElemElaboration ctx e e' dom,
                           ElemElimElaboration ctx (ImplicitPiElim head x dom cod (OmegaVarElim e' Id)) (ContextSubstElim cod (Ext Id (OmegaVarElim e' Id))) es meta ty])
  elabElemElimNu sig omega ctx head (ImplicitPiTy x dom cod) es meta ty = M.do
    (omega, e') <- liftUnifyM $ newElemMeta omega ctx dom SolveByUnification
    return (Success omega [ElemElimElaboration ctx (ImplicitPiElim head x dom cod (OmegaVarElim e' Id)) (ContextSubstElim cod (Ext Id (OmegaVarElim e' Id))) es meta ty])
  elabElemElimNu sig omega ctx head headTy [] meta ty = M.do
    -- We have to make sure that the head is rigid (so that it can't become {_ : _} → _ later)
    case !(Elab.liftM (isRigid sig omega headTy)) of
      True => M.do
        omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx headTy ty)
        let omega = instantiateByElaboration omega meta head
        return (Success omega [])
      False => return (Stuck "Head type is not rigid; headTy: \{renderDocNoAnn !(Elab.liftM $ prettyTyp sig omega (map fst ctx) headTy 0)}; expectedTy: \{renderDocNoAnn !(Elab.liftM $ prettyTyp sig omega (map fst ctx) ty 0)}")
  elabElemElimNu sig omega ctx head (PiTy x dom cod) ((_, Arg ([], e)) :: es) meta ty = M.do
    (omega, e') <- liftUnifyM $ newElemMeta omega ctx dom SolveByElaboration
    return (Success omega [ElemElaboration ctx e e' dom,
                           ElemElimElaboration ctx (PiElim head x dom cod (OmegaVarElim e' Id)) (ContextSubstElim cod (Ext Id (OmegaVarElim e' Id))) es meta ty])
  elabElemElimNu sig omega ctx head (SigmaTy x dom cod) ((_, Pi1) :: es) meta ty = M.do
    return (Success omega [ElemElimElaboration ctx (SigmaElim1 head x dom cod) dom es meta ty])
  elabElemElimNu sig omega ctx head (SigmaTy x dom cod) ((_, Pi2) :: es) meta ty = M.do
    return (Success omega [ElemElimElaboration ctx (SigmaElim2 head x dom cod) (ContextSubstElim cod (Ext Id (SigmaElim1 head x dom cod))) es meta ty])
  {- elabElemElimNu sig omega ctx head headTy args@(Arg ([], e) :: es) meta ty = M.do
    (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
    (omega, cod) <- liftUnifyM $ newTypeMeta omega (Ext ctx "_" (OmegaVarElim dom Id)) SolveByUnification
    omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx headTy (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)))
    return (Success omega [ElemElimElaboration ctx head (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)) args meta ty]) -}
  elabElemElimNu sig omega ctx head headTy elim meta ty =
    return (Stuck "Waiting on head")

  ||| Σ Ω Γ ⊦ (t : T) ⟦ē⟧ ⇝ t' : A
  public export
  elabElemElim : Params
              => Signature
              -> Omega
              -> Context
              -> CoreElem
              -> CoreTyp
              -> OpFreeElim
              -> OmegaName
              -> CoreTyp
              -> ElabM Elaboration.Result
  elabElemElim sig omega ctx head headTy es p ty = elabElemElimNu sig omega ctx head !(Elab.liftM $ openEval sig omega headTy) es p !(Elab.liftM $ openEval sig omega ty)

  public export
  elabEntry : Params
           => Signature
           -> Omega
           -> ElaborationEntry
           -> ElabM Elaboration.Result
  elabEntry sig omega (ElemElaboration ctx tm p ty) =
    elabElem sig omega ctx tm p ty
  elabEntry sig omega (TypeElaboration ctx tm p) =
    elabType sig omega ctx tm p
  elabEntry sig omega (ElemElimElaboration ctx head headTy es p ty) =
    elabElemElim sig omega ctx head headTy es p ty

  namespace Elaboration.Progress2
    ||| The intermediate results of solving a list of constraints (reflects whether at least some progress has been made).
    public export
    data Progress2 : Type where
      ||| We've traversed the list of pending elaboration problems once.
      ||| At least one step has been made.
      ||| We store a new Ω that can contain new holes and new constraints.
      ||| We store the list of problems to solve.
      Success : Omega -> List (ElaborationEntry, String) -> Progress2
      ||| We haven't progressed at all.
      Stuck : List (ElaborationEntry, String) -> Progress2
      ||| We've hit an error.
      Error : ElaborationEntry -> String -> Progress2

  progressEntriesH : Params
                  => Signature
                  -> Omega
                  -> (stuck : SnocList (ElaborationEntry, String))
                  -> List ElaborationEntry
                  -> Bool
                  -> ElabM Elaboration.Progress2.Progress2
  progressEntriesH sig cs stuck [] False = return (Stuck (cast stuck))
  progressEntriesH sig cs stuck [] True = return (Success cs (cast stuck))
  progressEntriesH sig cs stuck (e :: es) progressMade =
    case !(elabEntry sig cs e) of
      Success cs' new => progressEntriesH sig cs' stuck (new ++ es) True
      Stuck reason => progressEntriesH sig cs (stuck :< (e, reason)) es progressMade
      Error str => return (Error e str)

  progressEntries : Params
                 => Signature
                 -> Omega
                 -> List ElaborationEntry
                 -> ElabM Elaboration.Progress2.Progress2
  progressEntries sig cs list = progressEntriesH sig cs [<] list False

  ||| Try solving the problems in the list until either no constraints are left or each and every one is stuck.
  ||| Between rounds of solving problems we try solving unification problems.
  progressEntriesFixpoint : Params => Signature -> Omega -> List ElaborationEntry -> ElabM Elaboration.Fixpoint.Fixpoint
  progressEntriesFixpoint sig cs todo = M.do
    case containsNamedHolesOnly cs && isNil todo of
      True => return (Success cs)
      False => M.do
        case !(progressEntries sig cs todo) of
          Stuck stuckElaborations => M.do
            case !(liftUnifyM $ Unification.solve sig cs) of
              Stuck stuckConstraints => return (Stuck cs stuckElaborations stuckConstraints)
              Disunifier e err => return (Error cs (Right (e, err)))
              Success cs => progressEntriesFixpoint sig cs todo
          Error e str => return (Error cs (Left (e, str)))
          Success cs todo => progressEntriesFixpoint sig cs (map fst todo)

  ||| Try solving all elaboration and unification problems.
  public export
  solve : Params => Signature -> Omega -> List ElaborationEntry -> ElabM Elaboration.Fixpoint.Fixpoint
  solve sig omega todo = progressEntriesFixpoint sig omega todo

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
  Success omega <- solve sig omega probs
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

public export
elabFile : Params
        => Signature
        -> Omega
        -> SnocList Operator
        -> List1 TopLevel
        --                vvvvvv def name
        --                        vvvvv def range
        --                               vvvvvvvvv elaborated so far
        -> ElabM (Either (String, Range, Signature, TopLevelError) (Signature, Omega, SnocList Operator))
elabFile sig omega ops (Syntax r op ::: []) =
  return (Right (sig, omega, ops :< op))
elabFile sig omega ops (TypingSignature r x ty ::: []) = M.do
  -- write "Before shunting:\n\{show (TypingSignature r x ty)}"
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (TypingSignature r x ty))
    | Left err => return (Left (x, r, sig, err))
  return (Right (sig, omega, ops))
elabFile sig omega ops (LetSignature r x ty rhs ::: []) = M.do
  -- write "Before shunting:\n\{show (LetSignature r x ty rhs)}"
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (LetSignature r x ty rhs))
    | Left err => return (Left (x, r, sig, err))
  return (Right (sig, omega, ops))
elabFile sig omega ops (Syntax r op ::: e' :: es) = M.do
  elabFile sig omega (ops :< op) (e' ::: es)
elabFile sig omega ops (TypingSignature r x ty ::: e' :: es) = M.do
  -- write "Before shunting:\n\{show (TypingSignature r x ty)}"
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (TypingSignature r x ty))
    | Left err => return (Left (x, r, sig, err))
  elabFile sig omega ops (e' ::: es)
elabFile sig omega ops (LetSignature r x ty rhs ::: e' :: es) = M.do
  -- write "Before shunting:\n\{show (LetSignature r x ty rhs)}"
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (LetSignature r x ty rhs))
    | Left err => return (Left (x, r, sig, err))
  elabFile sig omega ops (e' ::: es)
elabFile sig omega ops (DefineSignature r x ty rhs ::: []) = M.do
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (DefineSignature r x ty rhs))
    | Left err => return (Left (x, r, sig, err))
  return (Right (sig, omega, ops))
elabFile sig omega ops (DefineSignature r x ty rhs ::: e' :: es) = M.do
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (DefineSignature r x ty rhs))
    | Left err => return (Left (x, r, sig, err))
  elabFile sig omega ops (e' ::: es)
