module Nova.Surface.Elaboration

import Data.AVL
import Data.List
import Data.List1
import Data.SnocList
import Data.Fin
import Data.Location

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Conversion
import Nova.Core.Evaluation
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Name
import Nova.Core.Pretty
import Nova.Core.Substitution
import Nova.Core.Unification

import Nova.Surface.Language
import Nova.Surface.Shunting
import Nova.Surface.Operator
import Nova.Surface.SemanticToken

CoreElem = Nova.Core.Language.D.Elem
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

public export
liftM : M a -> ElabM a
liftM f = M.do
  st <- get
  mapState (const st) (const ()) f

public export
liftMEither : MEither String a -> ElabM a
liftMEither f = M.do
 case !(liftM f) of
   Right x => return x
   Left err => throw err

public export
liftUnifyM : UnifyM a -> ElabM a
liftUnifyM f = M.do
  MkElabSt _ toks namedHoles <- get
  mapState (\u => MkElabSt u toks namedHoles) (.unifySt) f

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
  ElemElaboration : Context -> SurfaceTerm -> OmegaName -> CoreElem -> ElaborationEntry
  ||| Γ ⊦ ⟦A⟧ ⇝ A' type
  TypeElaboration : Context -> SurfaceTerm -> OmegaName -> ElaborationEntry
  ||| Γ ⊦ (t : T) ⟦ē⟧ ⇝ p : C
  ElemElimElaboration : Context -> CoreElem -> CoreElem -> OpFreeElim -> OmegaName -> CoreElem -> ElaborationEntry

public export
range : ElaborationEntry -> Range
range (ElemElaboration ctx tm n ty) = range tm
range (TypeElaboration ctx tm n) = range tm
range (ElemElimElaboration ctx head headTy [] n ty) = MkRange (0, 0) (0, 0) -- FIX: we need to come up with something in that case
range (ElemElimElaboration ctx head headTy ((r, _) :: _) n ty) = r

partial
public export
Show ElaborationEntry where
  show (ElemElaboration ctx tm p ty) = "... ⊦ ⟦\{show tm}⟧ ⇝ ... : ..."
  show (TypeElaboration ctx tm p) = "... ⊦ ⟦\{show tm}⟧ ⇝ ... type"
  show (ElemElimElaboration x y z xs str w) = "ElemElimElaboration"

namespace Elaboration
  public export
  data Result : Type where
    ||| Elaboration step has been made: new Ω that can contain new metas and new constraints.
    Success : Omega -> List ElaborationEntry -> Result
    ||| No elaboration step has been made.
    -- FIX: String ~> Doc Ann
    Stuck : String -> Result
    ||| Surface-level term can't be elaborated.
    -- FIX: String ~> Doc Ann
    Error : String -> Result

public export
instantiateByElaboration : Omega -> OmegaName -> Elem -> Omega
instantiateByElaboration omega idx rhs =
  case (lookup idx omega) of
    Just (MetaElem ctx ty SolveByElaboration) => insert (idx, LetElem ctx rhs ty) omega
    Just (MetaType ctx SolveByElaboration) => insert (idx, LetType ctx rhs) omega
    _ => assert_total $ idris_crash "instantiateByElaboration"

||| Γ₀ (xᵢ : A) Γ₁ ⊦ xᵢ : A
lookupContext : Context -> VarName -> Maybe (CoreElem, CoreElem)
lookupContext Empty x = Nothing
lookupContext (SignatureVarElim k) x = Nothing
lookupContext (Ext ctx x ty) y = M.do
  case x == y of
    True => Just (ContextVarElim 0, ContextSubstElim ty Wk)
    False => do
      (t, ty) <- lookupContext ctx y
      Just (ContextSubstElim t Wk, ContextSubstElim ty Wk)

||| Σ = Σ₀ (Δ ⊦ x : A) Σ₁
||| -----------------
||| Σ ⊦ Δ(↑(x Σ₁))
||| Σ Δ(↑(x Σ₁)) ⊦ A(↑(x Σ₁)) type
lookupSignature : Signature -> VarName -> Maybe (Context, Nat, CoreElem)
lookupSignature [<] x = Nothing
lookupSignature (sig :< (x, CtxEntry)) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupSignature (sig :< (x, TypeEntry {})) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupSignature (sig :< (x, EqTyEntry {})) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupSignature (sig :< (x, ElemEntry ctx ty)) y = M.do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim ty Wk)
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)
lookupSignature (sig :< (x, LetElemEntry ctx _ ty)) y = M.do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim ty Wk)
    False => do
      (ctx, i, ty) <- lookupSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim ty Wk)

lookupLetSignature : Signature -> VarName -> Maybe (Context, Nat, CoreElem, CoreElem)
lookupLetSignature [<] x = Nothing
lookupLetSignature (sig :< (x, CtxEntry)) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, rhs, ty) <- lookupLetSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
lookupLetSignature (sig :< (x, TypeEntry {})) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, rhs, ty) <- lookupLetSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
lookupLetSignature (sig :< (x, EqTyEntry {})) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, rhs, ty) <- lookupLetSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
lookupLetSignature (sig :< (x, ElemEntry ctx ty)) y = M.do
  case x == y of
    True => Nothing
    False => do
      (ctx, i, rhs, ty) <- lookupLetSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
lookupLetSignature (sig :< (x, LetElemEntry ctx rhs ty)) y = M.do
  case x == y of
    True => Just (subst ctx SubstSignature.Wk, 0, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)
    False => do
      (ctx, i, rhs, ty) <- lookupLetSignature sig y
      Just (subst ctx SubstSignature.Wk, S i, SignatureSubstElim rhs Wk, SignatureSubstElim ty Wk)

public export
pickPrefix : List (VarName, Elem) -> List VarName -> Maybe (List (VarName, Elem))
pickPrefix ctx [] = Just []
pickPrefix [] (x :: xs) = Nothing
pickPrefix ((x', ty) :: ctx) (x :: xs) =
  case (x' == x) of
    True => pickPrefix ctx xs <&> ((x, ty) ::)
    False => Nothing

||| Σ Ω Γ ⊦ ⟦t⟧ ⇝ p : A
||| A is head-neutral w.r.t. open evaluation.
public export
elabElemNu : Params
          => Signature
          -> Omega
          -> Context
          -> SurfaceTerm
          -> OmegaName
          -> CoreElem
          -> ElabM Elaboration.Result
elabElemNu sig omega ctx (PiTy r x dom cod) meta Universe = M.do
  (omega, dom') <- liftUnifyM $ newElemMeta omega ctx Universe SolveByElaboration
  (omega, cod') <- liftUnifyM $ newElemMeta omega (Ext ctx x (OmegaVarElim dom' Id)) Universe SolveByElaboration
  let omega = instantiateByElaboration omega meta (PiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  return (Success omega [ElemElaboration ctx dom dom' Universe, ElemElaboration (Ext ctx x (OmegaVarElim dom' Id)) cod cod' Universe])
elabElemNu sig omega ctx tm@(PiTy r x dom cod) meta ty = M.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty Universe)
  return (Success omega [ElemElaboration ctx tm meta Universe])
elabElemNu sig omega ctx (ImplicitPiTy r x dom cod) meta Universe = M.do
  (omega, dom') <- liftUnifyM $ newElemMeta omega ctx Universe SolveByElaboration
  (omega, cod') <- liftUnifyM $ newElemMeta omega (Ext ctx x (OmegaVarElim dom' Id)) Universe SolveByElaboration
  let omega = instantiateByElaboration omega meta (ImplicitPiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  return (Success omega [ElemElaboration ctx dom dom' Universe, ElemElaboration (Ext ctx x (OmegaVarElim dom' Id)) cod cod' Universe])
elabElemNu sig omega ctx tm@(ImplicitPiTy r x dom cod) meta ty = M.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty Universe)
  return (Success omega [ElemElaboration ctx tm meta Universe])
elabElemNu sig omega ctx (SigmaTy r x dom cod) meta Universe = M.do
  (omega, dom') <- liftUnifyM $ newElemMeta omega ctx Universe SolveByElaboration
  (omega, cod') <- liftUnifyM $ newElemMeta omega (Ext ctx x (OmegaVarElim dom' Id)) Universe SolveByElaboration
  let omega = instantiateByElaboration omega meta (SigmaTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  return (Success omega [ElemElaboration ctx dom dom' Universe, ElemElaboration (Ext ctx x (OmegaVarElim dom' Id)) cod cod' Universe])
elabElemNu sig omega ctx tm@(SigmaTy r x dom cod) meta ty = M.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty Universe)
  return (Success omega [ElemElaboration ctx tm meta Universe])
elabElemNu sig omega ctx (FunTy r dom cod) meta Universe = M.do
  (omega, dom') <- liftUnifyM $ newElemMeta omega ctx Universe SolveByElaboration
  (omega, cod') <- liftUnifyM $ newElemMeta omega ctx Universe SolveByElaboration
  let omega = instantiateByElaboration omega meta (PiTy "_" (OmegaVarElim dom' Id) (ContextSubstElim (OmegaVarElim cod' Id) Wk))
  return (Success omega [ElemElaboration ctx dom dom' Universe, ElemElaboration ctx cod cod' Universe])
elabElemNu sig omega ctx tm@(FunTy x y z) meta ty = M.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty Universe)
  return (Success omega [ElemElaboration ctx tm meta Universe])
elabElemNu sig omega ctx (ProdTy r dom cod) meta Universe = M.do
  (omega, dom') <- liftUnifyM $ newElemMeta omega ctx Universe SolveByElaboration
  (omega, cod') <- liftUnifyM $ newElemMeta omega ctx Universe SolveByElaboration
  let omega = instantiateByElaboration omega meta (SigmaTy "_" (OmegaVarElim dom' Id) (ContextSubstElim (OmegaVarElim cod' Id) Wk))
  return (Success omega [ElemElaboration ctx dom dom' Universe, ElemElaboration ctx cod cod' Universe])
elabElemNu sig omega ctx tm@(ProdTy x y z) meta ty = M.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty Universe)
  return (Success omega [ElemElaboration ctx tm meta Universe])
elabElemNu sig omega ctx (EqTy r a b t) meta Universe = M.do
  (omega, t') <- liftUnifyM $ newElemMeta omega ctx Universe SolveByElaboration
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
  let omega = instantiateByElaboration omega meta (EqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) (OmegaVarElim t' Id))
  return (Success omega [ElemElaboration ctx t t' Universe,
                         ElemElaboration ctx a a' (OmegaVarElim t' Id),
                         ElemElaboration ctx b b' (OmegaVarElim t' Id)
                        ]
         )
elabElemNu sig omega ctx tm@(EqTy r a b t) meta ty = M.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty Universe)
  return (Success omega [ElemElaboration ctx tm meta Universe])
elabElemNu sig omega ctx (PiVal r x f) meta (PiTy _ dom cod) = M.do
  (omega, f') <- liftUnifyM $ newElemMeta omega (Ext ctx x dom) cod SolveByElaboration
  let omega = instantiateByElaboration omega meta (PiVal x dom cod (OmegaVarElim f' Id))
  return (Success omega [ElemElaboration (Ext ctx x dom) f f' cod])
elabElemNu sig omega ctx tm@(PiVal r x f) meta ty = M.do
  (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, cod) <- liftUnifyM $ newTypeMeta omega (Ext ctx x (OmegaVarElim dom Id)) SolveByUnification
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty (PiTy x (OmegaVarElim dom Id) (OmegaVarElim cod Id)))
  return (Success omega [ElemElaboration ctx tm meta (PiTy x (OmegaVarElim dom Id) (OmegaVarElim cod Id))])
elabElemNu sig omega ctx (ImplicitPiVal r x f) meta (ImplicitPiTy _ dom cod) = M.do
  (omega, f') <- liftUnifyM $ newElemMeta omega (Ext ctx x dom) cod SolveByElaboration
  let omega = instantiateByElaboration omega meta (ImplicitPiVal x dom cod (OmegaVarElim f' Id))
  return (Success omega [ElemElaboration (Ext ctx x dom) f f' cod])
elabElemNu sig omega ctx tm@(ImplicitPiVal r x f) meta ty = M.do
  (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, cod) <- liftUnifyM $ newTypeMeta omega (Ext ctx x (OmegaVarElim dom Id)) SolveByUnification
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty (ImplicitPiTy x (OmegaVarElim dom Id) (OmegaVarElim cod Id)))
  return (Success omega [ElemElaboration ctx tm meta (ImplicitPiTy x (OmegaVarElim dom Id) (OmegaVarElim cod Id))])
elabElemNu sig omega ctx (SigmaVal r a b) meta (SigmaTy _ dom cod) = M.do
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx dom SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (ContextSubstElim cod (Ext Id (OmegaVarElim a' Id))) SolveByElaboration
  let omega = instantiateByElaboration omega meta (SigmaVal (OmegaVarElim a' Id) (OmegaVarElim b' Id))
  return (Success omega [ElemElaboration ctx a a' dom, ElemElaboration ctx b b' (ContextSubstElim cod (Ext Id (OmegaVarElim a' Id)))])
elabElemNu sig omega ctx tm@(SigmaVal r a b) meta ty = M.do
  (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, cod) <- liftUnifyM $ newTypeMeta omega (Ext ctx "_" (OmegaVarElim dom Id)) SolveByUnification
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)))
  return (Success omega [ElemElaboration ctx tm meta (SigmaTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))])
elabElemNu sig omega ctx (App r (Var r0 x) es) meta ty = M.do
  case lookupContext ctx x of
    Just (vTm, vTy) => M.do
      addSemanticToken (r0, BoundVarAnn)
      return (Success omega [ElemElimElaboration ctx vTm vTy es meta ty])
    Nothing =>
      case lookupSignature sig x of
        Just (Empty, idx, vTy) => M.do
          addSemanticToken (r0, ElimAnn)
          return (Success omega [ElemElimElaboration ctx (SignatureVarElim idx Terminal) vTy es meta ty])
        Just (sigCtx, idx, ty) =>
          return (Error "Non-empty signature context not supported yet for name: \{x}")
        Nothing => return (Error "Undefined name: \{x}")
elabElemNu sig omega ctx (App r (NatVal0 x) []) meta NatTy = M.do
  let omega = instantiateByElaboration omega meta NatVal0
  return (Success omega [])
elabElemNu sig omega ctx tm@(App r (NatVal0 x) []) meta ty = M.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty NatTy)
  return (Success omega [ElemElaboration ctx tm meta NatTy])
elabElemNu sig omega ctx (App r (NatVal0 x) (_ :: _)) meta ty =
  return (Error "Z applied to a spine")
elabElemNu sig omega ctx (App r (NatVal1 _) [(_, Arg ([], t))]) meta NatTy = M.do
  (omega, t') <- liftUnifyM $ newElemMeta omega ctx NatTy SolveByElaboration
  let omega = instantiateByElaboration omega meta (NatVal1 (OmegaVarElim t' Id))
  return (Success omega [ElemElaboration ctx t t' NatTy])
elabElemNu sig omega ctx tm@(App r (NatVal1 _) [t]) meta ty = M.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty NatTy)
  return (Success omega [ElemElaboration ctx tm meta NatTy])
elabElemNu sig omega ctx (App r (NatVal1 x) _) meta ty =
  return (Error "S applied to a wrong number of arguments")
elabElemNu sig omega ctx (App r (NatElim _) ((_, Arg ([x], schema)) :: (_, Arg ([], z)) :: (_, Arg ([y, h], s)) :: (_, Arg ([], t)) :: es)) meta ty = M.do
  (omega, schema') <- liftUnifyM $ newTypeMeta omega (Ext ctx x NatTy) SolveByElaboration
  (omega, z') <- liftUnifyM $ newElemMeta omega ctx (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)) SolveByElaboration
  (omega, s') <- liftUnifyM $ newElemMeta omega (Ext (Ext ctx y NatTy) h (OmegaVarElim schema' Id))
                                  (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))) SolveByElaboration
  (omega, t') <- liftUnifyM $ newElemMeta omega ctx NatTy SolveByElaboration
  return (Success omega [TypeElaboration (Ext ctx x NatTy) schema schema',
                         ElemElaboration ctx z z' (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)),
                         ElemElaboration (Ext (Ext ctx y NatTy) h (OmegaVarElim schema' Id)) s s' (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))),
                         ElemElaboration ctx t t' NatTy,
                         ElemElimElaboration ctx (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) (OmegaVarElim t' Id)) (OmegaVarElim schema' (Ext Id (OmegaVarElim t' Id))) es meta ty])
elabElemNu sig omega ctx (App r (NatElim _) _) meta ty =
  return (Error "S applied to a wrong number of arguments")
elabElemNu sig omega ctx (App _ (EqElim _) ((_, Arg ([], elemTy)) :: (_, Arg ([], a0)) :: (_, Arg ([x, h], schema)) :: (_, Arg ([], r)) :: (_, Arg ([], a1)) :: (_, Arg ([], e)) :: es)) meta ty = M.do
  (omega, t') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
  (omega, schema') <- liftUnifyM $ newTypeMeta omega (Ext (Ext ctx x (OmegaVarElim t' Id)) h (EqTy (ContextSubstElim (OmegaVarElim a' Id) Wk) CtxVar (ContextSubstElim (OmegaVarElim t' Id) Wk))) SolveByElaboration
  (omega, r') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim schema' (Ext (Ext Id (OmegaVarElim a' Id)) EqVal)) SolveByElaboration
  (omega, e') <- liftUnifyM $ newElemMeta omega ctx (EqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) (OmegaVarElim t' Id)) SolveByElaboration
  return (Success omega [TypeElaboration ctx elemTy t',
                         ElemElaboration ctx a0 a' (OmegaVarElim t' Id),
                         ElemElaboration ctx a1 b' (OmegaVarElim t' Id),
                         ElemElaboration ctx e e' (EqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) (OmegaVarElim t' Id)),
                         TypeElaboration (Ext (Ext ctx x (OmegaVarElim t' Id)) h (EqTy (ContextSubstElim (OmegaVarElim a' Id) Wk) CtxVar (ContextSubstElim (OmegaVarElim t' Id) Wk))) schema schema',
                         ElemElaboration ctx r r' (OmegaVarElim schema' (Ext (Ext Id (OmegaVarElim a' Id)) EqVal)),
                         ElemElimElaboration ctx (OmegaVarElim r' Id) (OmegaVarElim schema' (Ext (Ext Id (OmegaVarElim b' Id)) (OmegaVarElim e' Id))) es meta ty])
elabElemNu sig omega ctx (App r (EqElim x) _) meta ty =
  return (Error "J applied to a wrong number of arguments")
elabElemNu sig omega ctx (App r (EqVal x) []) meta (EqTy a b t) = M.do
  omega <- liftUnifyM $ addConstraint omega (ElemConstraint ctx a b t)
  let omega = instantiateByElaboration omega meta EqVal
  return (Success omega [])
elabElemNu sig omega ctx tm@(App r (EqVal x) []) meta ty = M.do
  (omega, t') <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByUnification
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByUnification
  let t = OmegaVarElim t' Id
  let a = OmegaVarElim a' Id
  let b = OmegaVarElim b' Id
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty (EqTy a b t))
  return (Success omega [ElemElaboration ctx tm meta (EqTy a b t)])
elabElemNu sig omega ctx (App r (EqVal x) _) meta ty = M.do
  return (Error "Refl applied to wrong number of arguments")
elabElemNu sig omega ctx (App r (NatTy x) []) meta Universe = M.do
  let omega = instantiateByElaboration omega meta NatTy
  return (Success omega [])
elabElemNu sig omega ctx tm@(App r (NatTy x) []) meta ty = M.do
  omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx ty Universe)
  return (Success omega [ElemElaboration ctx tm meta Universe])
elabElemNu sig omega ctx (App r (NatTy x) _) meta ty =
  return (Error "ℕ applied to a wrong number of arguments")
elabElemNu sig omega ctx (App r (UniverseTy x) []) meta ty =
  return (Error "We don't have 𝕌 : 𝕌!")
elabElemNu sig omega ctx (App r (UniverseTy x) _) meta ty =
  return (Error "𝕌 applied to a wrong number of arguments")
elabElemNu sig omega ctx (App r (UnnamedHole r0 Nothing) []) meta ty = M.do
  (omega, n) <- liftUnifyM $ newElemMeta omega ctx ty SolveByUnification
  let omega = instantiateByElaboration omega meta (OmegaVarElim n Id)
  return (Success omega [])
elabElemNu sig omega ctx (App r (UnnamedHole r0 (Just vars)) []) meta ty = M.do
  let Just regctx = asRegularContext ctx
     | Nothing => return (Error "Context is not regular")
  let Just regctxPrefix = pickPrefix (cast regctx) vars
    | Nothing => return (Error "Invalid context prefix")
  let ctxPrefix = fromRegularContext (cast regctxPrefix)
  (omega, n) <- liftUnifyM $ newElemMeta omega ctxPrefix ty SolveByUnification
  let omega = instantiateByElaboration omega meta (OmegaVarElim n (WkN (length regctx `minus` length regctxPrefix)))
  return (Success omega [])
elabElemNu sig omega ctx (App r (UnnamedHole x _) _) meta ty =
  return (Error "? applied to arguments not supported")
elabElemNu sig omega ctx (App r (Hole r0 n Nothing) es) meta ty = M.do
  case (lookup n omega) of
    Just _ => return (Error "Hole already exists: \{n}")
    Nothing => M.do
      omega <- liftUnifyM $ newElemMeta omega ctx n ty NoSolve
      let omega = instantiateByElaboration omega meta (OmegaVarElim n Id)
      addNamedHole (the Params %search).absFilePath r0 n
      return (Success omega [])
elabElemNu sig omega ctx (App r (Hole r0 n (Just vars)) es) meta ty = M.do
  case (lookup n omega) of
    Just _ => return (Error "Hole already exists: \{n}")
    Nothing => M.do
      let Just regctx = asRegularContext ctx
         | Nothing => return (Error "Context is not regular")
      let Just regctxPrefix = pickPrefix (cast regctx) vars
        | Nothing => return (Error "Invalid context prefix")
      let ctxPrefix = fromRegularContext (cast regctxPrefix)
      omega <- liftUnifyM $ newElemMeta omega ctxPrefix n ty SolveByUnification
      let omega = instantiateByElaboration omega meta (OmegaVarElim n (WkN (length regctx `minus` length regctxPrefix)))
      return (Success omega [])
elabElemNu sig omega ctx (App r (Unfold r0 x) []) meta ty = M.do
  case lookupLetSignature sig x of
    Just (Empty, idx, vRhs, vTy) =>
      return (Success omega [ElemElimElaboration ctx EqVal (EqTy (SignatureVarElim idx Id) vRhs vTy) [] meta ty])
    Just (sigCtx, idx, vRhs, vTy) =>
      return (Error "Non-empty signature context not supported yet for signature name: \{x}")
    Nothing => return (Error "Undefined signature name: \{x}")
elabElemNu sig omega ctx (App r (Unfold r0 x) _) meta ty = M.do
  return (Error "!\{x} applied to a wrong number of arguments")
-- Π-β A (x. B) (x. f) e : (x ↦ f) e ≡ f[e/x] ∈ B[e/x]
elabElemNu sig omega ctx (App r (PiBeta r0) [(_, Arg ([], dom)), (_, Arg ([x'], cod)), (_, Arg ([x], f)), (_, Arg ([], e))]) meta ty = M.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega (Ext ctx x (OmegaVarElim dom' Id)) SolveByElaboration
  (omega, f') <- liftUnifyM $ newElemMeta omega (Ext ctx x (OmegaVarElim dom' Id)) (OmegaVarElim cod' Id) SolveByElaboration
  (omega, e') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim dom' Id) SolveByElaboration
  return (Success omega [TypeElaboration ctx dom dom',
                         TypeElaboration (Ext ctx x' (OmegaVarElim dom' Id)) cod cod',
                         ElemElaboration (Ext ctx x (OmegaVarElim dom' Id)) f f' (OmegaVarElim cod' Id),
                         ElemElaboration ctx e e' (OmegaVarElim dom' Id),
                         ElemElimElaboration ctx EqVal (EqTy (PiElim (PiVal x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id) (OmegaVarElim f' Id)) x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id) (OmegaVarElim e' Id)) (OmegaVarElim f' (Ext Id (OmegaVarElim e' Id))) (OmegaVarElim cod' (Ext Id (OmegaVarElim e' Id)))) [] meta ty])
elabElemNu sig omega ctx (App r (PiBeta r0) _) meta ty =
  return (Error "Π-β applied to a wrong number of arguments")
-- Π-η f : (x ↦ f x) ≡ f ∈ (x : A) → B
elabElemNu sig omega ctx (App r (PiEta r0) [(_, Arg ([], f))]) meta ty = M.do
  (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, cod) <- liftUnifyM $ newTypeMeta omega (Ext ctx "_" (OmegaVarElim dom Id)) SolveByUnification
  (omega, f') <- liftUnifyM $ newElemMeta omega ctx (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)) SolveByElaboration
  return (Success omega [ElemElaboration ctx f f' (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id)),
                         ElemElimElaboration ctx EqVal (EqTy (PiVal "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id) (PiElim (OmegaVarElim f' Wk) "_" (OmegaVarElim dom Wk) (OmegaVarElim cod (Under Wk)) CtxVar)) (OmegaVarElim f' Id) (PiTy "_" (OmegaVarElim dom Id) (OmegaVarElim cod Id))) [] meta ty])
elabElemNu sig omega ctx (App r (PiEta r0) _) meta ty =
  return (Error "Π-η applied to a wrong number of arguments")
-- ℕ-β-Z (x. A) z (y. h. s) : ℕ-elim (x. A) z (y. h. s) Z ≡ z ∈ A[Z/x]
elabElemNu sig omega ctx (App r (NatBetaZ r0) ((_, Arg ([x], schema)) :: (_, Arg ([], z)) :: (_, Arg ([y, h], s)) :: [])) meta ty = M.do
  (omega, schema') <- liftUnifyM $ newTypeMeta omega (Ext ctx x NatTy) SolveByElaboration
  (omega, z') <- liftUnifyM $ newElemMeta omega ctx (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)) SolveByElaboration
  (omega, s') <- liftUnifyM $ newElemMeta omega (Ext (Ext ctx y NatTy) h (OmegaVarElim schema' Id))
                                  (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))) SolveByElaboration
  return (Success omega [TypeElaboration (Ext ctx x NatTy) schema schema',
                         ElemElaboration ctx z z' (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)),
                         ElemElaboration (Ext (Ext ctx y NatTy) h (OmegaVarElim schema' Id)) s s' (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))),
                         ElemElimElaboration ctx EqVal (EqTy (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) NatVal0) (OmegaVarElim z' Id) (OmegaVarElim schema' (Ext Id NatVal0))) [] meta ty])
elabElemNu sig omega ctx (App r (NatBetaZ r0) _) meta ty =
  return (Error "ℕ-β-Z applied to a wrong number of arguments")
-- ℕ-β-S (x. A) z (y. h. s) t : ℕ-elim (x. A) z (y. h. s) (S t) ≡ s[t/x, ℕ-elim (x. A) z (y. h. s) t/h] ∈ A[S t/x]
elabElemNu sig omega ctx (App r (NatBetaS r0) [(_, Arg ([x], schema)), (_, Arg ([], z)), (_, Arg ([y, h], s)), (_, Arg ([], t))]) meta ty = M.do
  (omega, schema') <- liftUnifyM $ newTypeMeta omega (Ext ctx x NatTy) SolveByElaboration
  (omega, z') <- liftUnifyM $ newElemMeta omega ctx (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)) SolveByElaboration
  (omega, s') <- liftUnifyM $ newElemMeta omega (Ext (Ext ctx y NatTy) h (OmegaVarElim schema' Id))
                                  (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))) SolveByElaboration
  (omega, t') <- liftUnifyM $ newElemMeta omega ctx NatTy SolveByElaboration
  return (Success omega [TypeElaboration (Ext ctx x NatTy) schema schema',
                         ElemElaboration ctx z z' (ContextSubstElim (OmegaVarElim schema' Id) (Ext Id NatVal0)),
                         ElemElaboration (Ext (Ext ctx y NatTy) h (OmegaVarElim schema' Id)) s s' (ContextSubstElim (OmegaVarElim schema' Id) (Ext (WkN 2) (NatVal1 (CtxVarN 1)))),
                         ElemElaboration ctx t t' NatTy,
                         ElemElimElaboration ctx EqVal (EqTy (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) (NatVal1 (OmegaVarElim t' Id))) (OmegaVarElim s' (Ext (Ext Id (OmegaVarElim t' Id)) (NatElim x (OmegaVarElim schema' Id) (OmegaVarElim z' Id) y h (OmegaVarElim s' Id) (OmegaVarElim t' Id)))) (OmegaVarElim schema' (Ext Id (NatVal1 (OmegaVarElim t' Id))))) [] meta ty])
elabElemNu sig omega ctx (App r (NatBetaS r0) _) meta ty =
  return (Error "ℕ-β-S applied to a wrong number of arguments")
-- Π⁼ (x. f) (y. g) (z. p) : (x ↦ f) ≡ (y ↦ g) ∈ (z : A) → B
elabElemNu sig omega ctx (App r (PiEq r0) [(_, Arg ([x], f)), (_, Arg ([y], g)), (_, Arg ([z], p))]) meta ty = M.do
  (omega, dom) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, cod) <- liftUnifyM $ newTypeMeta omega (Ext ctx z (OmegaVarElim dom Id)) SolveByUnification
  (omega, f') <- liftUnifyM $ newElemMeta omega (Ext ctx x (OmegaVarElim dom Id)) (OmegaVarElim cod Id) SolveByElaboration
  (omega, g') <- liftUnifyM $ newElemMeta omega (Ext ctx y (OmegaVarElim dom Id)) (OmegaVarElim cod Id) SolveByElaboration
  (omega, p') <- liftUnifyM $ newElemMeta omega (Ext ctx z (OmegaVarElim dom Id)) (EqTy (OmegaVarElim f' Id) (OmegaVarElim g' Id) (OmegaVarElim cod Id)) SolveByElaboration
  return (Success omega [ElemElaboration (Ext ctx x (OmegaVarElim dom Id)) f f' (OmegaVarElim cod Id),
                         ElemElaboration (Ext ctx y (OmegaVarElim dom Id)) g g' (OmegaVarElim cod Id),
                         ElemElaboration (Ext ctx z (OmegaVarElim dom Id)) p p' (EqTy (OmegaVarElim f' Id) (OmegaVarElim g' Id) (OmegaVarElim cod Id)),
                         ElemElimElaboration ctx EqVal (EqTy (PiVal x (OmegaVarElim dom Id) (OmegaVarElim cod Id) (OmegaVarElim f' Id))
                                                             (PiVal y (OmegaVarElim dom Id) (OmegaVarElim cod Id) (OmegaVarElim g' Id))
                                                             (PiTy z (OmegaVarElim dom Id) (OmegaVarElim cod Id))) [] meta ty])
elabElemNu sig omega ctx (App r (PiEq r0) _) meta ty =
  return (Error "Π⁼ applied to a wrong number of arguments")
elabElemNu sig omega ctx (App r (Tm _ tm) es) meta ty = M.do
  (omega, t) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  (omega, tm') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t Id) SolveByElaboration
  return (Success omega [ElemElaboration ctx tm tm' (OmegaVarElim t Id),
                         ElemElimElaboration ctx (OmegaVarElim tm' Id) (OmegaVarElim t Id) es meta ty])

||| Σ Ω Γ ⊦ ⟦t⟧ ⇝ p : A
public export
elabElem : Params
        => Signature
        -> Omega
        -> Context
        -> SurfaceTerm
        -> OmegaName
        -> CoreElem
        -> ElabM Elaboration.Result
elabElem sig omega ctx tm p ty = elabElemNu sig omega ctx tm p !(liftM $ openEval sig omega ty)

||| Σ Ω Γ ⊦ ⟦A⟧ ⇝ A' type
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
  (omega, cod') <- liftUnifyM $ newTypeMeta omega (Ext ctx x (OmegaVarElim dom' Id)) SolveByElaboration
  let omega = instantiateByElaboration omega meta (PiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  return (Success omega [TypeElaboration ctx dom dom', TypeElaboration (Ext ctx x (OmegaVarElim dom' Id)) cod cod'])
elabType sig omega ctx (ImplicitPiTy r x dom cod) meta = M.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega (Ext ctx x (OmegaVarElim dom' Id)) SolveByElaboration
  let omega = instantiateByElaboration omega meta (ImplicitPiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  return (Success omega [TypeElaboration ctx dom dom', TypeElaboration (Ext ctx x (OmegaVarElim dom' Id)) cod cod'])
elabType sig omega ctx (SigmaTy r x dom cod) meta = M.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega (Ext ctx x (OmegaVarElim dom' Id)) SolveByElaboration
  let omega = instantiateByElaboration omega meta (SigmaTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))
  return (Success omega [TypeElaboration ctx dom dom', TypeElaboration (Ext ctx x (OmegaVarElim dom' Id)) cod cod'])
elabType sig omega ctx (FunTy r dom cod) meta = M.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  let omega = instantiateByElaboration omega meta (PiTy "_" (OmegaVarElim dom' Id) (ContextSubstElim (OmegaVarElim cod' Id) Wk))
  return (Success omega [TypeElaboration ctx dom dom', TypeElaboration ctx cod cod'])
elabType sig omega ctx (ProdTy r dom cod) meta = M.do
  (omega, dom') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, cod') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  let omega = instantiateByElaboration omega meta (SigmaTy "_" (OmegaVarElim dom' Id) (ContextSubstElim (OmegaVarElim cod' Id) Wk))
  return (Success omega [TypeElaboration ctx dom dom', TypeElaboration ctx cod cod'])
elabType sig omega ctx (EqTy r a b t) meta = M.do
  (omega, t') <- liftUnifyM $ newTypeMeta omega ctx SolveByElaboration
  (omega, a') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
  (omega, b') <- liftUnifyM $ newElemMeta omega ctx (OmegaVarElim t' Id) SolveByElaboration
  let omega = instantiateByElaboration omega meta (EqTy (OmegaVarElim a' Id) (OmegaVarElim b' Id) (OmegaVarElim t' Id))
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
elabType sig omega ctx tm@(App r (Var r0 x) es) meta =
  return (Success omega [ElemElaboration ctx tm meta Universe])
elabType sig omega ctx (App r (NatVal0 x) _) meta = M.do
  return (Error "Z is not a type")
elabType sig omega ctx (App r (NatVal1 _) _) meta = M.do
  return (Error "S is not a type")
elabType sig omega ctx (App r (NatElim _) _) meta = M.do
  return (Error "ℕ-elim is not a type")
elabType sig omega ctx (App _ (EqElim _) _) meta = M.do
  return (Error "J is not a type")
elabType sig omega ctx (App r (EqVal x) _) meta = M.do
  return (Error "Refl is not a type")
elabType sig omega ctx (App r (NatTy x) []) meta = M.do
  let omega = instantiateByElaboration omega meta NatTy
  return (Success omega [])
elabType sig omega ctx (App r (NatTy x) _) meta =
  return (Error "ℕ applied to a wrong number of arguments")
elabType sig omega ctx (App r (UniverseTy x) []) meta = M.do
  let omega = instantiateByElaboration omega meta Universe
  return (Success omega [])
elabType sig omega ctx (App r (UniverseTy x) _) meta =
  return (Error "𝕌 applied to a wrong number of arguments")
elabType sig omega ctx (App r (UnnamedHole r0 Nothing) []) meta = M.do
  (omega, n) <- liftUnifyM $ newTypeMeta omega ctx SolveByUnification
  let omega = instantiateByElaboration omega meta (OmegaVarElim n Id)
  return (Success omega [])
elabType sig omega ctx (App r (UnnamedHole r0 (Just vars)) []) meta = M.do
  let Just regctx = asRegularContext ctx
     | Nothing => return (Error "Context is not regular")
  let Just regctxPrefix = pickPrefix (cast regctx) vars
    | Nothing => return (Error "Invalid context prefix")
  let ctxPrefix = fromRegularContext (cast regctxPrefix)
  (omega, n) <- liftUnifyM $ newTypeMeta omega ctxPrefix SolveByUnification
  let omega = instantiateByElaboration omega meta (OmegaVarElim n (WkN (length regctx `minus` length regctxPrefix)))
  return (Success omega [])
elabType sig omega ctx (App r (UnnamedHole x vars) _) meta =
  return (Error "? applied to arguments not supported")
elabType sig omega ctx (App r (Hole r0 n Nothing) es) meta =
  case (lookup n omega) of
    Just _ => return (Error "Hole already exists: \{n}")
    Nothing => M.do
      omega <- liftUnifyM $ newTypeMeta omega ctx n NoSolve
      let omega = instantiateByElaboration omega meta (OmegaVarElim n Id)
      addNamedHole (the Params %search).absFilePath r0 n
      return (Success omega [])
elabType sig omega ctx (App r (Hole r0 n (Just vars)) es) meta =
  case (lookup n omega) of
    Just _ => return (Error "Hole already exists: \{n}")
    Nothing => M.do
      let Just regctx = asRegularContext ctx
         | Nothing => return (Error "Context is not regular")
      let Just regctxPrefix = pickPrefix (cast regctx) vars
        | Nothing => return (Error "Invalid context prefix")
      let ctxPrefix = fromRegularContext (cast regctxPrefix)
      omega <- liftUnifyM $ newTypeMeta omega ctxPrefix n SolveByUnification
      let omega = instantiateByElaboration omega meta (OmegaVarElim n (WkN (length regctx `minus` length regctxPrefix)))
      return (Success omega [])
elabType sig omega ctx (App r (Unfold r0 x) _) meta = M.do
  return (Error "! is not a type")
elabType sig omega ctx (App r (PiBeta r0) _) meta = M.do
  return (Error "Π-β is not a type")
elabType sig omega ctx (App r (PiEta r0) _) meta = M.do
  return (Error "Π-η is not a type")
elabType sig omega ctx (App r (NatBetaZ r0) _) meta = M.do
  return (Error "ℕ-β-Z is not a type")
elabType sig omega ctx (App r (NatBetaS r0) _) meta = M.do
  return (Error "ℕ-β-S is not a type")
elabType sig omega ctx (App r (PiEq r0) _) meta = M.do
  return (Error "Π⁼ is not a type")
elabType sig omega ctx (App r (Tm _ tm) []) meta = M.do
  return (Success omega [TypeElaboration ctx tm meta])
elabType sig omega ctx (App r (Tm _ tm) es) meta = M.do
  return (Error "_ _ is not a type")

||| Σ Ω Γ ⊦ (t : T) ⟦ē⟧ ⇝ t' : A
||| Where T is head-neutral w.r.t. open evaluation.
public export
elabElemElimNu : Params
              => Signature
              -> Omega
              -> Context
              -> CoreElem
              -> CoreElem
              -> OpFreeElim
              -> OmegaName
              -> CoreElem
              -> ElabM Elaboration.Result
elabElemElimNu sig omega ctx head (ImplicitPiTy x dom cod) ((_, ImplicitArg e) :: es) meta ty = M.do
  (omega, e') <- liftUnifyM $ newElemMeta omega ctx dom SolveByElaboration
  return (Success omega [ElemElaboration ctx e e' dom,
                         ElemElimElaboration ctx (ImplicitPiElim head x dom cod (OmegaVarElim e' Id)) (ContextSubstElim cod (Ext Id (OmegaVarElim e' Id))) es meta ty])
elabElemElimNu sig omega ctx head (ImplicitPiTy x dom cod) es meta ty = M.do
  (omega, e') <- liftUnifyM $ newElemMeta omega ctx dom SolveByUnification
  return (Success omega [ElemElimElaboration ctx (ImplicitPiElim head x dom cod (OmegaVarElim e' Id)) (ContextSubstElim cod (Ext Id (OmegaVarElim e' Id))) es meta ty])
elabElemElimNu sig omega ctx head headTy [] meta ty = M.do
  -- We have to make sure that the head is is rigid (so that it can't become {_ : _} → _ later)
  case !(liftM (isRigid sig omega headTy)) of
    True => M.do
      omega <- liftUnifyM $ addConstraint omega (TypeConstraint ctx headTy ty)
      let omega = instantiateByElaboration omega meta head
      return (Success omega [])
    False => return (Stuck "Head type is not rigid; headTy: \{renderDocNoAnn !(liftM $ prettyElem sig omega (map fst (tail ctx)) headTy 0)}; expectedTy: \{renderDocNoAnn !(liftM $ prettyElem sig omega (map fst (tail ctx)) ty 0)}")
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
  return (Stuck "Waiting on head, head: \{renderDocNoAnn !(liftM $ prettyElem sig omega (map fst (tail ctx)) head 0)}; headTy: \{renderDocNoAnn !(liftM $ prettyElem sig omega (map fst (tail ctx)) headTy 0)}; elim: \{show elim}")

||| Σ Ω Γ ⊦ (t : T) ⟦ē⟧ ⇝ t' : A
public export
elabElemElim : Params
            => Signature
            -> Omega
            -> Context
            -> CoreElem
            -> CoreElem
            -> OpFreeElim
            -> OmegaName
            -> CoreElem
            -> ElabM Elaboration.Result
elabElemElim sig omega ctx head headTy es p ty = elabElemElimNu sig omega ctx head !(liftM $ openEval sig omega headTy) es p !(liftM $ openEval sig omega ty)

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
    Success : Omega -> List ElaborationEntry -> Progress2
    ||| We haven't progressed at all.
    Stuck : List (ElaborationEntry, String) -> Progress2
    ||| We've hit an error.
    Error : ElaborationEntry -> String -> Progress2

||| Try solving the constraints in the list by passing through it once.
progressEntries : Params
               => Signature
               -> Omega
               -> (stuck : SnocList ElaborationEntry)
               -> List ElaborationEntry
               -> Bool
               -> ElabM Elaboration.Progress2.Progress2
progressEntries sig cs stuck [] False = return (Stuck [])
progressEntries sig cs stuck [] True = return (Success cs (cast stuck))
progressEntries sig cs stuck (e :: es) progressMade =
  case !(elabEntry sig cs e) of
    Success cs' new => progressEntries sig cs' stuck (new ++ es) True
    Stuck str =>
      case !(progressEntries sig cs (stuck :< e) es progressMade) of
        Stuck list => return (Stuck ((e, str) :: list))
        Success cs' new => return (Success cs' new)
        Error e s => return (Error e s)
    Error str => return (Error e str)

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

||| Try solving the problems in the list until either no constraints are left or each and every one is stuck.
||| Between rounds of solving problems we try solving unification problems.
progressEntriesFixpoint : Params => Signature -> Omega -> List ElaborationEntry -> ElabM Elaboration.Fixpoint.Fixpoint
progressEntriesFixpoint sig cs todo = M.do
  case containsNamedHolesOnly cs && isNil todo of
    True => return (Success cs)
    False => M.do
      case !(progressEntries sig cs [<] todo False) of
        Stuck stuckElaborations => M.do
          case !(liftUnifyM $ Unification.solve sig cs) of
            Stuck stuckConstraints => return (Stuck cs stuckElaborations stuckConstraints)
            Disunifier e err => return (Error cs (Right (e, err)))
            Success cs => progressEntriesFixpoint sig cs todo
        Error e str => return (Error cs (Left (e, str)))
        Success cs' todo => progressEntriesFixpoint sig cs' todo

||| Try solving all elaboration and unification problems.
public export
solve : Params => Signature -> Omega -> List ElaborationEntry -> ElabM Elaboration.Fixpoint.Fixpoint
solve sig omega todo = progressEntriesFixpoint sig omega todo

namespace TopLevelError
  public export
  data TopLevelError : Type where
    Stuck : Omega -> List (ElaborationEntry, String) -> List (ConstraintEntry, String) -> TopLevelError
    UnificationError : Omega -> (ConstraintEntry, String) -> TopLevelError
    ElaborationError : Omega -> (ElaborationEntry, String) -> TopLevelError

  public export
  pretty : Signature -> TopLevelError -> M (Doc Ann)
  pretty sig (Stuck omega stuckElab stuckCons) = M.do
    return $
      "----------- Stuck unification constraints: -------------"
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
      "----------- Stuck elaboration constraints: -------------"
       <+>
      vsep !(forList stuckElab $ \(elab, err) => M.do
        return $
          pretty (show elab)
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
  (omega, ty') <- liftUnifyM $ newTypeMeta omega Empty SolveByElaboration
  let probs = [TypeElaboration Empty ty ty']
  Success omega <- solve sig omega probs
    | Stuck omega stuckElab stuckCons => return (Left (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => return (Left (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => return (Left (UnificationError omega (con, err)))
  let sig = sig :< (x, ElemEntry Empty (OmegaVarElim ty' Id))
  let omega = subst omega Wk
  return (Right (sig, omega))
elabTopLevelEntry sig omega (LetSignature r x ty rhs) = M.do
  print_ Debug STDOUT "Elaborating \{x}"
  (omega, ty') <- liftUnifyM $ newTypeMeta omega Empty SolveByElaboration
  (omega, rhs') <- liftUnifyM $ newElemMeta omega Empty (OmegaVarElim ty' Id) SolveByElaboration
  let probs = [TypeElaboration Empty ty ty', ElemElaboration Empty rhs rhs' (OmegaVarElim ty' Id)]
  Success omega <- solve sig omega probs
    | Stuck omega stuckElab stuckCons => return (Left (Stuck omega stuckElab stuckCons))
    | Error omega (Left (elab, err)) => return (Left (ElaborationError omega (elab, err)))
    | Error omega (Right (con, err)) => return (Left (UnificationError omega (con, err)))
  let sig = sig :< (x, LetElemEntry Empty (OmegaVarElim rhs' Id) (OmegaVarElim ty' Id))
  let omega = subst omega Wk
  return (Right (sig, omega))

public export
elabFile : Params
        => Signature
        -> Omega
        -> SnocList Operator
        -> List1 TopLevel
        --                vvvvvv def name
        --                        vvvvv def range
        -> ElabM (Either (String, Range, TopLevelError) (Signature, Omega, SnocList Operator))
elabFile sig omega ops (Syntax r op ::: []) =
  return (Right (sig, omega, ops :< op))
elabFile sig omega ops (TypingSignature r x ty ::: []) = M.do
  -- write "Before shunting:\n\{show (TypingSignature r x ty)}"
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (TypingSignature r x ty))
    | Left err => return (Left (x, r, err))
  return (Right (sig, omega, ops))
elabFile sig omega ops (LetSignature r x ty rhs ::: []) = M.do
  -- write "Before shunting:\n\{show (LetSignature r x ty rhs)}"
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (LetSignature r x ty rhs))
    | Left err => return (Left (x, r, err))
  return (Right (sig, omega, ops))
elabFile sig omega ops (Syntax r op ::: e' :: es) = M.do
  elabFile sig omega (ops :< op) (e' ::: es)
elabFile sig omega ops (TypingSignature r x ty ::: e' :: es) = M.do
  -- write "Before shunting:\n\{show (TypingSignature r x ty)}"
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (TypingSignature r x ty))
    | Left err => return (Left (x, r, err))
  elabFile sig omega ops (e' ::: es)
elabFile sig omega ops (LetSignature r x ty rhs ::: e' :: es) = M.do
  -- write "Before shunting:\n\{show (LetSignature r x ty rhs)}"
  Right (sig, omega) <- elabTopLevelEntry sig omega !(liftMEither $ shuntTopLevel (cast ops) (LetSignature r x ty rhs))
    | Left err => return (Left (x, r, err))
  elabFile sig omega ops (e' ::: es)
