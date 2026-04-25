module Nova.Core.Unification

import Me.Russoul.Data.Location

import Data.List
import Data.SnocList
import Data.Util
import Data.Maybe
import Data.AVL
import Data.Fin

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Control.Monad.Id
import Nova.Control.Monad.St
import Nova.Control.Monad.MaybeSt
import Nova.Control.Monad.Reader

import Nova.Core.Conversion
import Nova.Core.Context
import Nova.Core.Evaluation
import Nova.Core.Language
import Nova.Core.Pretty
import Nova.Core.Rigidity
import Nova.Core.Substitution

import Nova.Surface.SemanticToken

infixl 5 <||>

-- Unification is performed relative to a sub-relation of definitional equality:
-- (~) implies (=)

public export
record UnifySt where
  constructor MkUnifySt
  nextOmegaIdx : Nat

public export
initialUnifySt : UnifySt
initialUnifySt = MkUnifySt 0

||| The error type is a type represents critical unexpected unrecoverable errors.
||| By design, we are not supposed to ever try/catch those!
||| Don't use CriticalError for any other kind of error (e.g. recoverable / expected).
public export
UnifyM : Type -> Type
UnifyM = St UnifySt

namespace UnifyM
  public export
  liftEvalM : EvalM a -> UnifyM a
  liftEvalM = St.liftId

  namespace Maybe
    public export
    liftEvalM : EvalM a -> UnifyM (Maybe a)
    liftEvalM = (Just <$>) . St.liftId

public export
nextOmegaName : UnifyM OmegaName
nextOmegaName = St.do
  MkUnifySt idx <- get
  put (MkUnifySt (S idx))
  pure ("?\{show idx}")

public export
nextOmegaIdx : UnifyM Nat
nextOmegaIdx = St.do
  MkUnifySt idx <- get
  put (MkUnifySt (S idx))
  pure idx

%hide UnifyM.Maybe.liftEvalM

namespace Result
  ||| Unification step result while solving a constraint.
  public export
  data Result : Type where
    ||| A step has been made.
    Success : List ConstraintEntry -> (newMetas : List (Context, OmegaName, Either () Typ)) -> (sols : List (OmegaName, Either Typ Elem)) -> Result
    ||| A step has *not* been made.
    Stuck : String -> Result
    ||| Constraint is contradictive.
    Disunifier : String -> Result

mutual
  namespace SubstContextNF
    -- σ : Γ ⇒ Δ
    -- τ : Γ ⇒ Ξ
    -- ? : Δ ⇒ Ξ such that ? ∘ σ ~ τ
    --
    public export
    invert : Signature
          -> Omega
          -> (sigma : SubstContext)
          -> (tau : SubstContextNF)
          -> (gamma : Context)
          -> (delta : Context)
          -> (xi : Context)
          -> Maybe SubstContext
    invert sig omega sigma Terminal gamma delta xi = Prelude.pure Terminal
    -- σ : Γ₀ Γ₁ ⇒ Δ
    -- ↑(Γ₁) : Γ₀ Γ₁ ⇒ Γ₀
    -- ? : Δ ⇒ Γ₀ such that ? ∘ σ ~ ↑(Γ₁)
    --
    -- in that case ↑ᵏ = ·
    invert sig omega sigma (WkN k) gamma delta [<] = Prelude.pure Terminal
    -- in that case ↑ᵏ = (↑ᵏ⁺¹, k)
    invert sig omega sigma (WkN k) gamma delta xi@(_ :< _) =
      SubstContextNF.invert sig omega sigma (Ext (WkN (S k)) (ContextVarElim k)) gamma delta xi
    invert sig omega sigma (Ext tau t) gamma delta (xi :< _) = Prelude.do
      tau' <- invert sig omega sigma tau gamma delta xi
      t' <- invert sig omega gamma delta sigma t
      pure (Ext tau' t')
    invert sig omega sigma (Ext tau t) gamma delta _ = Prelude.do
      assert_total $ idris_crash "SubstContextNF.invert(Ext)"

  namespace SubstContext
    -- σ : Γ ⇒ Δ
    -- τ : Γ ⇒ Ω
    -- ? : Δ ⇒ Ω such that ? ∘ σ ~ τ
    --
    public export
    invert : Signature
          -> Omega
          -> (sigma : SubstContext)
          -> (tau : SubstContext)
          -> (gamma : Context)
          -> (delta : Context)
          -> (omega : Context)
          -> Maybe SubstContext
    invert sig omega sigma tau = invert sig omega sigma (eval tau)

  namespace Typ
    -- Substitution x̄ can only be a mixture of permutation and deletition.
    -- Then solution for y:
    -- y(x̄) = x
    -- is unique if it exists.
    -- Γ ⊦ A
    -- σ : Γ ⇒ Δ
    public export
    invertNu : Signature
            -> Omega
            -> (gamma : Context)
            -> (delta : Context)
            -> (sigma : SubstContext)
            -> (t : Typ)
            -> Maybe Typ
    invertNu sig omega ctx delta sigma (PiTy x dom cod) = Prelude.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      pure (PiTy x dom' cod')
    invertNu sig omega ctx delta sigma (ImplicitPiTy x dom cod) = Prelude.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      pure (ImplicitPiTy x dom' cod')
    invertNu sig omega ctx delta sigma (SigmaTy x dom cod) = Prelude.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      pure (SigmaTy x dom' cod')
    invertNu sig omega ctx delta sigma NatTy = Prelude.pure NatTy
    invertNu sig omega ctx delta sigma ZeroTy = Prelude.pure ZeroTy
    invertNu sig omega ctx delta sigma OneTy = Prelude.pure OneTy
    invertNu sig omega ctx delta sigma UniverseTy = Prelude.pure UniverseTy
    invertNu sig omega ctx delta sigma (El a) = Prelude.do
      a' <- invert sig omega ctx delta sigma a
      pure (El a')
    invertNu sig omega ctx delta sigma (ContextSubstElim x y) = assert_total $ idris_crash "invertNu(ContextSubstElim)"
    invertNu sig omega ctx delta sigma (SignatureSubstElim x y) = assert_total $ idris_crash "invertNu(SignatureSubstElim)"
    invertNu sig omega ctx delta sigma (OmegaVarElim k tau) = Prelude.do
      tau' <- invert sig omega sigma tau ctx delta getOmega
      pure (OmegaVarElim k tau')
     where
      getOmega : Context
      getOmega =
        case (lookup k omega) of
          Nothing => assert_total $ idris_crash "invertNu(OmegaVarElim)(1)"
          Just (LetElem xi {}) => assert_total $ idris_crash "invertNu(OmegaVarElim)(2)"
          Just (MetaElem xi {}) => assert_total $ idris_crash "invertNu(OmegaVarElim)(3)"
          Just (LetType xi {}) => xi
          Just (MetaType xi {}) => xi
          Just _ => assert_total $ idris_crash "invertNu(OmegaVarElim)(4)"
    invertNu sig omega ctx delta sigma (TyEqTy a b) = Prelude.do
      a <- invert sig omega ctx delta sigma a
      b <- invert sig omega ctx delta sigma b
      pure (TyEqTy a b)
    invertNu sig omega ctx delta sigma (ElEqTy a b ty) = Prelude.do
      a <- invert sig omega ctx delta sigma a
      b <- invert sig omega ctx delta sigma b
      ty <- invert sig omega ctx delta sigma ty
      pure (ElEqTy a b ty)
    invertNu sig omega ctx delta sigma (SignatureVarElim k tau) = Prelude.do
      tau' <- invert sig omega sigma tau ctx delta getCtx
      pure (SignatureVarElim k tau')
     where
      getCtx : Context
      getCtx =
        case (splitAt sig k) of
          Nothing => assert_total $ idris_crash "invertNu(SignatureVarElim)(1)"
          Just (_, (_, e), rest) =>
            case subst e (WkN $ 1 + length rest) of
             TypeEntry xi {} => xi
             LetTypeEntry xi rhs => xi
             ElemEntry {} => assert_total $ idris_crash "invertNu(SignatureVarElim)(ElemEntry)"
             LetElemEntry {} => assert_total $ idris_crash "invertNu(SignatureVarElim)(LetElemEntry)"

    public export
    invert : Signature -> Omega -> Context -> Context -> SubstContext -> Typ -> Maybe Typ
    invert sig omega ctx delta sigma tm = Prelude.do
      invertNu sig omega ctx delta sigma (openEval sig omega tm)

  namespace Elem
    -- Substitution x̄ can only be a mixture of permutation and deletion.
    -- Then solution for y:
    -- y(x̄) = x
    -- is unique if it exists.
    -- Γ ⊦ t
    -- σ : Γ ⇒ Δ
    public export
    invertNu : Signature
            -> Omega
            -> (gamma : Context)
            -> (delta : Context)
            -> (sigma : SubstContext)
            -> (t : Elem)
            -> Maybe Elem
    invertNu sig omega ctx delta sigma (PiTy x dom cod) = Prelude.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, El dom)) (delta :< (x, El dom')) (Under sigma) cod
      pure (PiTy x dom' cod')
    invertNu sig omega ctx delta sigma (ImplicitPiTy x dom cod) = Prelude.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, El dom)) (delta :< (x, El dom')) (Under sigma) cod
      pure (ImplicitPiTy x dom' cod')
    invertNu sig omega ctx delta sigma (SigmaTy x dom cod) = Prelude.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, El dom)) (delta :< (x, El dom')) (Under sigma) cod
      pure (SigmaTy x dom' cod')
    invertNu sig omega ctx delta sigma (PiVal x dom cod f) = Prelude.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      f' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) f
      pure (PiVal x dom' cod' f')
    invertNu sig omega ctx delta sigma (ImplicitPiVal x dom cod f) = Prelude.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      f' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) f
      pure (ImplicitPiVal x dom' cod' f')
    invertNu sig omega ctx delta sigma (SigmaVal x dom cod p q) = Prelude.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      p' <- invert sig omega ctx delta sigma p
      q' <- invert sig omega ctx delta sigma q
      pure (SigmaVal x dom' cod' p' q')
    invertNu sig omega ctx delta sigma (PiElim f x dom cod e) = Prelude.do
      f' <- invert sig omega ctx delta sigma f
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      e' <- invert sig omega ctx delta sigma e
      pure (PiElim f' x dom' cod' e')
    invertNu sig omega ctx delta sigma (ImplicitPiElim f x dom cod e) = Prelude.do
      f' <- invert sig omega ctx delta sigma f
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      e' <- invert sig omega ctx delta sigma e
      pure (ImplicitPiElim f' x dom' cod' e')
    invertNu sig omega ctx delta sigma (SigmaElim1 f x dom cod) = Prelude.do
      f' <- invert sig omega ctx delta sigma f
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      pure (SigmaElim1 f' x dom' cod')
    invertNu sig omega ctx delta sigma (SigmaElim2 f x dom cod) = Prelude.do
      f' <- invert sig omega ctx delta sigma f
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      pure (SigmaElim2 f' x dom' cod')
    invertNu sig omega ctx delta sigma NatVal0 = Prelude.do pure NatVal0
    invertNu sig omega ctx delta sigma (NatVal1 t) = Prelude.do
      t <- invert sig omega ctx delta sigma t
      pure (NatVal1 t)
    invertNu sig omega ctx delta sigma NatTy = Prelude.pure NatTy
    invertNu sig omega ctx delta sigma ZeroTy = Prelude.pure ZeroTy
    invertNu sig omega ctx delta sigma OneTy = Prelude.pure OneTy
    invertNu sig omega ctx delta sigma OneVal = Prelude.pure OneVal
    invertNu sig omega ctx delta sigma (ZeroElim ty t) = Prelude.do
      ty' <- invert sig omega ctx delta sigma ty
      t' <- invert sig omega ctx delta sigma t
      pure (ZeroElim ty' t')
    invertNu sig omega ctx delta sigma (NatElim x schema z y h s t) = Prelude.do
      schema' <- invert sig omega (ctx :< (x, NatTy)) (delta :< (x, NatTy)) (Under sigma) schema
      z' <- invert sig omega ctx delta sigma z
      s' <- invert sig omega (ctx :< (y, NatTy) :< (h, schema)) (delta :< (y, NatTy) :< (h,  schema')) (Under (Under sigma)) s
      t' <- invert sig omega ctx delta sigma t
      pure (NatElim x schema' z' y h s' t')
    invertNu sig omega ctx delta sigma (ContextSubstElim x y) = assert_total $ idris_crash "invertNu(ContextSubstElim)"
    invertNu sig omega ctx delta sigma (SignatureSubstElim x y) = assert_total $ idris_crash "invertNu(SignatureSubstElim)"
    invertNu sig omega ctx delta sigma (ContextVarElim k) = Prelude.do
      index <- go sigma 0
      pure (ContextVarElim index)
     where
      mutual
        goNu : SubstContextNF -> Nat -> Maybe Nat
        goNu Terminal index = Nothing
        -- ↑ⁱ
        goNu (WkN i) index =
          case k >= i of
            -- We won't find k
            False => Nothing
            -- We'll find k
            True => Just (index + (k `minus` i))
        -- due to the conditions imposed on σ, t must be a variable up to (~)
        goNu (Ext sigma t) index = Prelude.do
          case openEval sig omega t of
            ContextVarElim i =>
              case (i == k) of
                True => Just index
                False => go sigma (S index)
            _ => assert_total $ idris_crash "invertNu(ContextVarElim)"

        go : SubstContext -> Nat -> Maybe Nat
        go sigma index = goNu (eval sigma) index
    -- σ : Γ ⇒ Δ
    -- Γ ⊦ χᵢ (τ : Γ ⇒ Ω)
    -- Δ ⊦ χᵢ (ρ : Δ ⇒ Ω)
    -- Γ ⊦ χᵢ (ρ ∘ σ) = χᵢ τ
    -- that is, we need to find ρ : Δ ⇒ Ω
    -- such that (ρ ∘ σ) ~ τ
    invertNu sig omega ctx delta sigma (SignatureVarElim k tau) = Prelude.do
      tau' <- invert sig omega sigma tau ctx delta getCtx
      pure (SignatureVarElim k tau')
     where
      getCtx : Context
      getCtx =
        case splitAt sig k of
          Nothing => assert_total $ idris_crash "invertNu(SignatureVarElim)(1)"
          Just (_, (_, e), rest) =>
            case subst e (WkN $ 1 + length rest) of
             ElemEntry xi {} => xi
             LetElemEntry xi {} => xi
             TypeEntry {} => assert_total $ idris_crash "invertNu(SignatureVarElim)(TypeEntry)"
             LetTypeEntry {} => assert_total $ idris_crash "invertNu(SignatureVarElim)(LetTypeEntry)"
    invertNu sig omega ctx delta sigma (OmegaVarElim k tau) = Prelude.do
      tau' <- invert sig omega sigma tau ctx delta getOmega
      pure (OmegaVarElim k tau')
     where
      getOmega : Context
      getOmega =
        case (lookup k omega) of
          Nothing => assert_total $ idris_crash "invertNu(OmegaVarElim)(1)"
          Just (LetElem xi {}) => xi
          Just (MetaElem xi {}) => xi
          Just (LetType xi {}) => assert_total $ idris_crash "invertNu(OmegaVarElim)(2)"
          Just (MetaType xi {}) => assert_total $ idris_crash "invertNu(OmegaVarElim)(3)"
          Just _ => assert_total $ idris_crash "invertNu(OmegaVarElim)(4)"
    invertNu sig omega ctx delta sigma (TyEqTy a b) = Prelude.do
      a <- invert sig omega ctx delta sigma a
      b <- invert sig omega ctx delta sigma b
      pure (TyEqTy a b)
    invertNu sig omega ctx delta sigma (ElEqTy a b ty) = Prelude.do
      a <- invert sig omega ctx delta sigma a
      b <- invert sig omega ctx delta sigma b
      ty <- invert sig omega ctx delta sigma ty
      pure (ElEqTy a b ty)
    invertNu sig omega ctx delta sigma (TyEqVal ty) = Prelude.do
      ty' <- invert sig omega ctx delta sigma ty
      pure (TyEqVal ty')
    invertNu sig omega ctx delta sigma (ElEqVal ty e) = Prelude.do
      ty' <- invert sig omega ctx delta sigma ty
      e' <- invert sig omega ctx delta sigma e
      pure (ElEqVal ty' e')

    public export
    invert : Signature -> Omega -> Context -> Context -> SubstContext -> Elem -> Maybe Elem
    invert sig omega ctx delta sigma tm = invertNu sig omega ctx delta sigma (openEval sig omega tm)

mutual
  public export
  preinvertibleNu : Signature -> Omega -> SubstContextNF -> Set Nat -> Bool
  preinvertibleNu sig omega Terminal vars = True
  preinvertibleNu sig omega (WkN k) vars = True
  preinvertibleNu sig omega (Ext sigma t) vars = do
    case (openEval sig omega t) of
      ContextVarElim k =>
        (not $ isElem k vars) `and` preinvertible sig omega sigma (insert k vars)
      _ => pure False

  ||| Substitution is pre-invertible if
  ||| it consists of permutations and deletions of variables (up to (~)).
  public export
  preinvertible : Signature -> Omega -> SubstContext -> Set Nat -> Bool
  preinvertible sig omega sigma vars = preinvertibleNu sig omega (eval sigma) vars

mutual
  namespace SubstContextNF
    public export
    occurs : Signature -> Omega -> SubstContextNF -> OmegaName -> Bool
    occurs sig omega Terminal k = False
    occurs sig omega (WkN j) k = False
    occurs sig omega (Ext sigma t) k = occurs sig omega sigma k || occurs sig omega t k

  namespace SubstContext
    public export
    occurs : Signature -> Omega -> SubstContext -> OmegaName -> Bool
    occurs sig omega sigma k = occurs sig omega (eval sigma) k

  namespace Typ
    public export
    occursNu : Signature -> Omega -> Typ -> OmegaName -> Bool
    occursNu sig omega (PiTy x dom cod) k =
      occurs sig omega dom k || occurs sig omega cod k
    occursNu sig omega (ImplicitPiTy x dom cod) k =
      occurs sig omega dom k || occurs sig omega cod k
    occursNu sig omega (SigmaTy x dom cod) k =
      occurs sig omega dom k || occurs sig omega cod k
    occursNu sig omega NatTy k = False
    occursNu sig omega ZeroTy k = False
    occursNu sig omega OneTy k = False
    occursNu sig omega UniverseTy k = False
    occursNu sig omega (El a) k = occurs sig omega a k
    occursNu sig omega (ContextSubstElim x y) k = assert_total $ idris_crash "occursNu(ContextSubstElim)"
    occursNu sig omega (SignatureSubstElim x y) k = assert_total $ idris_crash "occursNu(SignatureSubstElim)"
    occursNu sig omega (OmegaVarElim j sigma) k = j == k || occurs sig omega sigma k
    occursNu sig omega (TyEqTy a b) k = occurs sig omega a k || occurs sig omega b k
    occursNu sig omega (ElEqTy a b ty) k = occurs sig omega a k || occurs sig omega b k || occurs sig omega ty k
    occursNu sig omega (SignatureVarElim j sigma) k = occurs sig omega sigma k

    public export
    occurs : Signature -> Omega -> Typ -> OmegaName -> Bool
    occurs sig omega t k = occursNu sig omega (openEval sig omega t) k

  namespace Elem
    public export
    occursNu : Signature -> Omega -> Elem -> OmegaName -> Bool
    occursNu sig omega (PiTy x dom cod) k =
      occurs sig omega dom k || occurs sig omega cod k
    occursNu sig omega (ImplicitPiTy x dom cod) k =
      occurs sig omega dom k || occurs sig omega cod k
    occursNu sig omega (SigmaTy x dom cod) k =
      occurs sig omega dom k || occurs sig omega cod k
    occursNu sig omega (PiVal x dom cod f) k =
      occurs sig omega dom k || occurs sig omega cod k || occurs sig omega f k
    occursNu sig omega (ImplicitPiVal x dom cod f) k =
      occurs sig omega dom k || occurs sig omega cod k || occurs sig omega f k
    occursNu sig omega (SigmaVal x a b p q) k =
      occurs sig omega a k || occurs sig omega b k || occurs sig omega p k || occurs sig omega q k
    occursNu sig omega (PiElim f x dom cod e) k =
      occurs sig omega f k || occurs sig omega dom k || occurs sig omega cod k || occurs sig omega e k
    occursNu sig omega (ImplicitPiElim f x dom cod e) k =
      occurs sig omega f k || occurs sig omega dom k || occurs sig omega cod k || occurs sig omega e k
    occursNu sig omega (SigmaElim1 f x dom cod) k =
      occurs sig omega f k || occurs sig omega dom k || occurs sig omega cod k
    occursNu sig omega (SigmaElim2 f x dom cod) k =
      occurs sig omega f k || occurs sig omega dom k || occurs sig omega cod k
    occursNu sig omega NatVal0 k = False
    occursNu sig omega (NatVal1 t) k = occurs sig omega t k
    occursNu sig omega NatTy k = False
    occursNu sig omega ZeroTy k = False
    occursNu sig omega OneTy k = False
    occursNu sig omega OneVal k = False
    occursNu sig omega (ZeroElim ty t) k =
      occurs sig omega ty k || occurs sig omega t k
    occursNu sig omega (NatElim x schema z y h s t) k =
      occurs sig omega schema k || occurs sig omega z k || occurs sig omega s k || occurs sig omega t k
    occursNu sig omega (ContextSubstElim x y) k = assert_total $ idris_crash "occursNu(ContextSubstElim)"
    occursNu sig omega (SignatureSubstElim x y) k = assert_total $ idris_crash "occursNu(SignatureSubstElim)"
    occursNu sig omega (ContextVarElim j) k = pure False
    occursNu sig omega (SignatureVarElim j sigma) k = occurs sig omega sigma k
    occursNu sig omega (OmegaVarElim j sigma) k = pure (j == k) || occurs sig omega sigma k
    occursNu sig omega (TyEqTy a b) k = occurs sig omega a k || occurs sig omega b k
    occursNu sig omega (ElEqTy a b ty) k = occurs sig omega a k || occurs sig omega b k || occurs sig omega ty k
    occursNu sig omega (TyEqVal ty) k =
      occurs sig omega ty k
    occursNu sig omega (ElEqVal ty e) k =
      occurs sig omega ty k || occurs sig omega e k

    public export
    occurs : Signature -> Omega -> Elem -> OmegaName -> Bool
    occurs sig omega t k = occursNu sig omega (openEval sig omega t) k

||| Σ Ω Γ ⊦ ? σ ~ t : A
public export
trySolveElem : Signature -> Omega -> Context -> OmegaName -> Context -> Typ -> SubstContext -> Elem -> Typ -> EvalM Result
trySolveElem sig omega ctx holeIdx holeCtx holeTy sigma rhs ty = Id.do
  -- Δ ⊦ ? : C
  -- Γ ⊦ ?(x̄) ~ t : A
  -- *) make sure t doesn't contain ?
  -- *) make sure x̄ is permutations and deletions of variables
  -- x̄ : Γ ⇒ Δ
  -- Note that by typing: (Γ ⊦ C(x̄) = A)
  -- we need to find a unique (up to (~)):
  -- Δ ⊦ t' : C
  -- such that
  -- Γ ⊦ t'(x̄) ~ t : A
  -- TODO: do we actually have a guarantee that t' : C ???
  -- then
  -- Δ ⊦ ? ≔ t' : C
  let False = occurs sig omega rhs holeIdx
    | True => pure (Stuck "Occurs check failed") -- TODO: strengthen the check to a disunifier in some cases
  let True = preinvertible sig omega sigma empty
    | False => pure (Stuck "Substitution is not invertible")
  Just rhs' <- invert sig omega ctx holeCtx sigma rhs
    | Nothing => pure (Stuck "Can't invert RHS")
  pure (Success [] [] [(holeIdx, Right rhs')])

||| Σ Ω Γ ⊦ ? σ ~ A type
public export
trySolveType : Signature -> Omega -> Context -> OmegaName -> Context -> SubstContext -> Typ -> EvalM Result
trySolveType sig omega ctx holeIdx holeCtx sigma rhs = Id.do
  -- Δ ⊦ ? : C
  -- Γ ⊦ ?(x̄) ~ t : A
  -- *) make sure t doesn't contain ?
  -- *) make sure x̄ is permutations and deletions of variables
  -- x̄ : Γ ⇒ Δ
  -- Note that by typing: (Γ ⊦ C(x̄) = A)
  -- we need to find a unique (up to (~)):
  -- Δ ⊦ t' : C
  -- such that
  -- Γ ⊦ t'(x̄) ~ t : A
  -- TODO: do we actually have a guarantee that t' : C ???
  -- then
  -- Δ ⊦ ? ≔ t' : C
  let False = occurs sig omega rhs holeIdx
    | True => pure (Stuck "Occurs check failed") -- TODO: strengthen the check to a disunifier in some cases
  let True = preinvertible sig omega sigma empty
    | False => pure (Stuck "Substitution is not invertible")
  Just rhs' <- invert sig omega ctx holeCtx sigma rhs
    | Nothing => pure (Stuck "Can't invert RHS")
  pure (Success [] [] [(holeIdx, Left rhs')])


namespace Elem

  public export
  unifyElemElimNu : Signature -> Omega -> Context -> Elem -> Elem -> UnifyM Result
  unifyElemElimNu sig omega ctx (PiElim f0 x dom cod e0) (PiElim f1 _ _ _ e1) = St.do
    case !(unifyElemElimNu sig omega ctx f0 f1) of
      Success cons metas lets =>
        pure (Success (ElemConstraint ctx e0 e1 dom :: cons) metas lets)
      nope => pure nope
  unifyElemElimNu sig omega ctx (ImplicitPiElim f0 x dom cod e0) (ImplicitPiElim f1 _ _ _ e1) = St.do
    case !(unifyElemElimNu sig omega ctx f0 f1) of
      Success cons metas lets =>
        pure (Success (ElemConstraint ctx e0 e1 dom :: cons) metas lets)
      nope => pure nope
  unifyElemElimNu sig omega ctx (SigmaElim1 f0 x dom cod) (SigmaElim1 f1 _ _ _) = St.do
    case !(unifyElemElimNu sig omega ctx f0 f1) of
      Success cons metas lets => pure (Success cons metas lets)
      nope => pure nope
  unifyElemElimNu sig omega ctx (SigmaElim2 f0 x dom cod) (SigmaElim2 f1 _ _ _) = St.do
    case !(unifyElemElimNu sig omega ctx f0 f1) of
      Success cons metas lets => pure (Success cons metas lets)
      nope => pure nope
  unifyElemElimNu sig omega ctx (ZeroElim _ t0) (ZeroElim _ t1) = St.do
    case !(unifyElemElimNu sig omega ctx t0 t1) of
      Success cons metas lets => pure (Success cons metas lets)
      nope => pure nope
  unifyElemElimNu sig omega ctx (NatElim x0 schema0 z0 y0 h0 s0 t0) (NatElim x1 schema1 z1 y1 h1 s1 t1) = St.do
    case !(unifyElemElimNu sig omega ctx t0 t1) of
      Success cons metas lets =>
        pure (Success (     TypeConstraint (ctx :< (x0, NatTy)) schema0 schema1
                           :: ElemConstraint ctx z0 z1 (ContextSubstElim schema0 (Ext Id NatVal0))
                           :: ElemConstraint (ctx :< (x0, NatTy) :< (h0, schema0)) s0 s1 (ContextSubstElim schema0 (Ext (Chain Wk Wk) (NatVal1 (NatVal1 (CtxVarN 1)))))
                           :: cons
                        )
                        metas lets
              )
      nope => pure nope
      -- ||| Xᵢ(σ)
      -- SignatureVarElim : Nat -> SubstContext -> Elem
      -- ||| Xᵢ(σ)
      -- OmegaVarElim : OmegaName -> SubstContext -> Elem
  unifyElemElimNu sig omega ctx (ContextVarElim x0) (ContextVarElim x1) = St.do
    case (x0 == x1) of
      True => pure (Success [] [] [])
      False => pure (Disunifier "xᵢ ~ xⱼ where i ≠ j")
  unifyElemElimNu sig omega ctx (SignatureVarElim x0 sigma0) (SignatureVarElim x1 sigma1) = St.do
    case (x0 == x1) of
      True => St.do
        let Just (_, delta) = with [Prelude.(<&>)] Index.lookupSignature sig x0 <&> mapSnd getContext
          | Nothing => assert_total $ idris_crash "unifyElemElimNu(1)"
        pure (Success [SubstContextConstraint sigma0 sigma1 ctx delta] [] [])
      False => pure (Disunifier "xᵢ ~ xⱼ where i ≠ j")
  unifyElemElimNu sig omega ctx _ _ = pure (Stuck "Elim rule doesn't apply")

  ||| Σ Ω Γ ⊦ a₀ ~ a₁ : A
  ||| A, a₀, a₁ are head-neutral w.r.t. substitution.
  public export
  unifyElemMetaNu : Signature -> Omega -> Context -> Elem -> Elem -> Typ -> UnifyM Result
  unifyElemMetaNu sig cs ctx a@(OmegaVarElim k0 sigma0) b@(OmegaVarElim k1 sigma1) ty = St.do
    let Just entry0 = lookup k0 cs
         | _ => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim(1))"
    let Just entry1 = lookup k1 cs
         | _ => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim(2))"
    case (entry0, entry1) of
      -- Both sides are holes, try solving for each side.
      (MetaElem hctx0 hty0 SolveByUnification, MetaElem hctx1 hty1 SolveByUnification) => St.do
         case !(UnifyM.liftEvalM $ trySolveElem sig cs ctx k0 hctx0 hty0 sigma0 b ty) of
           Success cs [] sols => pure (Success cs [] sols)
           Success cs (_ :: _) sols => assert_total $ idris_crash "unifyElemNu(Meta, Meta)"
           Stuck _ => UnifyM.liftEvalM $ trySolveElem sig cs ctx k1 hctx1 hty1 sigma1 a ty
           Disunifier dis => pure (Disunifier dis)
      -- One side is a hole
      (MetaElem hctx0 hty0 SolveByUnification, _) =>
        liftEvalM $ trySolveElem sig cs ctx k0 hctx0 hty0 sigma0 b ty
      -- One side is a hole
      (_, MetaElem hctx1 hty1 SolveByUnification) =>
        liftEvalM $ trySolveElem sig cs ctx k1 hctx1 hty1 sigma1 a ty
      -- Both sides are rigid
      (e, _) => St.do
        case (!(liftEvalM $ isRigid sig cs a) && !(liftEvalM $ isRigid sig cs b)) of
          True =>
           case (k0 == k1) of
             False => pure (Disunifier "χᵢ vs χⱼ, where i ≠ j")
             True =>
               case e of
                 LetElem target {} => pure (Success [SubstContextConstraint sigma0 sigma1 ctx target] [] [])
                 _ => assert_total $ idris_crash "unifyElemMetaNu(SignatureVarElim, SignatureVarElim)(1)"
          False => pure (Stuck "χᵢ vs χⱼ, where i ≠ j, flex")
  unifyElemMetaNu sig cs ctx a@(OmegaVarElim k sigma) b ty = St.do
    -- we now that b is rigid here
    case !(liftEvalM $ isRigid sig cs a) of
      True => pure (Disunifier "rigid χᵢ vs something else rigid")
      False => St.do
       let Just entry = lookup k cs
            | _ => assert_total $ idris_crash "unifyElemNu(SignatureVarElim(3))"
       case entry of
         -- We've got a hole, try solving it
         MetaElem hctx hty SolveByUnification => liftEvalM $ trySolveElem sig cs ctx k hctx hty sigma b ty
         MetaElem hctx hty SolveByElaboration => pure (Stuck "?(solve by elaboration) vs something else rigid")
         MetaElem hctx hty NoSolve => pure (Stuck "?(no solve) vs something else rigid")
         MetaType {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(1)"
         LetElem {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(2)"
         LetType {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(3)"
         TypeConstraint {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(4)"
         ElemConstraint {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(5)"
         SubstContextConstraint {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(6)"
  unifyElemMetaNu sig cs ctx a b@(OmegaVarElim k sigma) ty = St.do
    -- we now that a is rigid here
    case !(liftEvalM $ isRigid sig cs b) of
      True => pure (Disunifier "rigid χᵢ vs something else rigid")
      False => St.do
       let Just entry = lookup k cs
            | _ => assert_total $ idris_crash "unifyElemMetaNu(SignatureVarElim(3))"
       case entry of
         -- We've got a hole, try solving it
         MetaElem hctx hty SolveByUnification => liftEvalM $ trySolveElem sig cs ctx k hctx hty sigma a ty
         MetaElem hctx hty SolveByElaboration => pure (Stuck "?(solve by elaboration) vs something else rigid")
         MetaElem hctx hty NoSolve => pure (Stuck "?(no solve) vs something else rigid")
         MetaType {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(1)"
         LetElem {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(2)"
         LetType {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(3)"
         TypeConstraint {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(4)"
         ElemConstraint {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(5)"
         SubstContextConstraint {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(6)"
  unifyElemMetaNu sig cs ctx a b ty = pure (Stuck "unifyMetaNu rule doesn't apply")

  ||| Σ Ω Γ ⊦ a₀ ~ a₁ : A
  ||| A, a₀, a₁ are head-neutral w.r.t. substitution.
  public export
  unifyElemIntroNu : Signature -> Omega -> Context -> Elem -> Elem -> Typ -> UnifyM Result
  unifyElemIntroNu sig cs ctx (PiTy x0 dom0 cod0) (PiTy x1 dom1 cod1) ty = St.do
    pure (Success [ ElemConstraint ctx dom0 dom1 UniverseTy
                    , ElemConstraint (ctx :< (x0, El dom0)) cod0 cod1 UniverseTy
                    ]
                    []
                    []
           )
  unifyElemIntroNu sig cs ctx (ImplicitPiTy x0 dom0 cod0) (ImplicitPiTy x1 dom1 cod1) ty = St.do
    pure (Success [ ElemConstraint ctx dom0 dom1 UniverseTy
                    , ElemConstraint (ctx :< (x0, El dom0)) cod0 cod1 UniverseTy
                    ]
                    []
                    []
           )
  unifyElemIntroNu sig cs ctx (SigmaTy x0 dom0 cod0) (SigmaTy x1 dom1 cod1) ty = St.do
    pure (Success [ ElemConstraint ctx dom0 dom1 UniverseTy
                    , ElemConstraint (ctx :< (x0, El dom0)) cod0 cod1 UniverseTy
                    ]
                    []
                    []
           )
  unifyElemIntroNu sig cs ctx (PiVal x0 dom0 cod0 f0) (PiVal x1 dom1 cod1 f1) ty = St.do
    pure (Success [ElemConstraint (ctx :< (x0, dom0)) f0 f1 cod0]
                    []
                    []
           )
  unifyElemIntroNu sig cs ctx (ImplicitPiVal x0 dom0 cod0 f0) (ImplicitPiVal x1 dom1 cod1 f1) ty = St.do
    pure (Success [ElemConstraint (ctx :< (x0, dom0)) f0 f1 cod0]
                    []
                    []
           )
  unifyElemIntroNu sig cs ctx (SigmaVal x a b p0 q0) (SigmaVal _ _ _ p1 q1) _ = St.do
    pure (Success [ElemConstraint ctx p0 p1 a, ElemConstraint ctx q0 q1 (ContextSubstElim b (Ext Id p0))]
                    []
                    []
           )
  unifyElemIntroNu sig cs ctx NatVal0 NatVal0 ty =
    St.pure (Success [] [] [])
  unifyElemIntroNu sig cs ctx OneVal OneVal _ =
    St.pure (Success [] [] [])
  unifyElemIntroNu sig cs ctx (NatVal1 t0) (NatVal1 t1) ty = M.do
    St.pure (Success [ ElemConstraint ctx t0 t1 NatTy] [] [])
  unifyElemIntroNu sig cs ctx NatTy NatTy ty = St.pure (Success [] [] [])
  unifyElemIntroNu sig cs ctx ZeroTy ZeroTy ty = St.pure (Success [] [] [])
  unifyElemIntroNu sig cs ctx OneTy OneTy ty = St.pure (Success [] [] [])
  unifyElemIntroNu sig cs ctx (ContextSubstElim x y) b ty = assert_total $ idris_crash "unifyElemIntroNu(ContextSubstElim)"
  unifyElemIntroNu sig cs ctx (SignatureSubstElim x y) b ty = assert_total $ idris_crash "unifyElemIntroNu(SignatureSubstElim)"
  unifyElemIntroNu sig cs ctx (TyEqTy p0 q0) (TyEqTy p1 q1) _ = St.do
    pure (Success [  ElemConstraint ctx p0 p1 UniverseTy,
                       ElemConstraint ctx q0 q1 UniverseTy] [] [])
  unifyElemIntroNu sig cs ctx (ElEqTy p0 q0 ty0) (ElEqTy p1 q1 ty1) _ = St.do
    pure (Success [  ElemConstraint ctx ty0 ty1 UniverseTy,
                       ElemConstraint ctx p0 p1 (El ty0),
                       ElemConstraint ctx q0 q1 (El ty0)] [] [])
  unifyElemIntroNu sig cs ctx (TyEqVal _) (TyEqVal _) ty = pure (Success [] [] [])
  unifyElemIntroNu sig cs ctx (ElEqVal _ _) (ElEqVal _ _) ty = pure (Success [] [] [])
  unifyElemIntroNu sig cs ctx a b ty = pure (Stuck "UnifyElemIntroNu rule doesn't apply")

  public export
  (<||>) : UnifyM Result -> UnifyM Result -> UnifyM Result
  ma <||> mb = St.do
    case !ma of
      Disunifier err => St.pure (Disunifier err)
      Success a b c => St.pure (Success a b c)
      Stuck _ => mb

  public export
  unifyElem : Signature -> Omega -> Context -> Elem -> Elem -> Typ -> UnifyM Result
  unifyElem sig cs ctx a b ty = St.do
    a <- liftEvalM $ openEval sig cs a
    b <- liftEvalM $ openEval sig cs b
    ty <- liftEvalM $ openEval sig cs ty
    (unifyElemMetaNu sig cs ctx a b ty <||> unifyElemElimNu sig cs ctx a b <||> unifyElemIntroNu sig cs ctx a b ty)

namespace Type'
  ||| Assumes that RHS isn't El, even if rigid.
  public export
  unifyElAgainstRigid : Signature -> Omega -> Context -> Elem -> Typ -> UnifyM Result
  unifyElAgainstRigid sig omega ctx el ZeroTy = St.do
    pure (Success [ ElemConstraint ctx el ZeroTy UniverseTy] [] [])
  unifyElAgainstRigid sig omega ctx el OneTy = St.do
    pure (Success [ ElemConstraint ctx el OneTy UniverseTy] [] [])
  -- El ? = 𝕌 type <=> ⊥
  unifyElAgainstRigid sig omega ctx el UniverseTy = St.do
    pure (Disunifier "El ? = 𝕌 doesn't have solutions for ?")
  unifyElAgainstRigid sig omega ctx el (SignatureVarElim {}) = St.do
    pure (Stuck "El ? = Xᵢ σ")
  unifyElAgainstRigid sig omega ctx el NatTy = St.do
    pure (Success [ ElemConstraint ctx el NatTy UniverseTy] [] [])
  unifyElAgainstRigid sig omega ctx el (PiTy x dom cod) = St.do
    dom' <- nextOmegaName
    cod' <- nextOmegaName
    pure (Success [ ElemConstraint ctx el (PiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id)) UniverseTy
                     -- Original problem still persists, but gets simplified!
                    , TypeConstraint ctx (El (PiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))) (PiTy x dom cod)
                    ]
                    [(ctx, dom', Right UniverseTy), (ctx :< (x, El $ OmegaVarElim dom' Id), cod', Right UniverseTy)]
                    []
           )
  unifyElAgainstRigid sig omega ctx el (ImplicitPiTy x dom cod) = St.do
    dom' <- nextOmegaName
    cod' <- nextOmegaName
    pure (Success [ ElemConstraint ctx el (ImplicitPiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id)) UniverseTy
                     -- Original problem still persists, but gets simplified!
                    , TypeConstraint ctx (El (ImplicitPiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))) (ImplicitPiTy x dom cod)
                    ]
                    [(ctx, dom', Right UniverseTy), (ctx :< (x, El $ OmegaVarElim dom' Id), cod', Right UniverseTy)]
                    []
           )
  unifyElAgainstRigid sig omega ctx el (SigmaTy x dom cod) = St.do
    dom' <- nextOmegaName
    cod' <- nextOmegaName
    pure (Success [ElemConstraint ctx el (SigmaTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id)) UniverseTy
                     -- Original problem still persists, but gets simplified!
                    , TypeConstraint ctx (El (SigmaTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))) (SigmaTy x dom cod)
                    ]
                    [(ctx, dom', Right UniverseTy), (ctx :< (x, El $ OmegaVarElim dom' Id), cod', Right UniverseTy)]
                    []
           )
  unifyElAgainstRigid sig omega ctx el (TyEqTy a0 a1) = St.do
    a0' <- nextOmegaName
    a1' <- nextOmegaName
    pure (Success [ElemConstraint ctx el (TyEqTy (OmegaVarElim a0' Id) (OmegaVarElim a1' Id)) UniverseTy
                     -- Original problem still persists, but gets simplified!
                    , TypeConstraint ctx (El $ TyEqTy (OmegaVarElim a0' Id) (OmegaVarElim a1' Id)) (TyEqTy a0 a1)
                    ]
                    [(ctx, a0', Right UniverseTy), (ctx, a1', Right UniverseTy)]
                    []
           )
  unifyElAgainstRigid sig omega ctx el (ElEqTy a0 a1 ty) = St.do
    a0' <- nextOmegaName
    a1' <- nextOmegaName
    ty' <- nextOmegaName
    pure (Success [ElemConstraint ctx el (ElEqTy (OmegaVarElim a0' Id) (OmegaVarElim a1' Id) (OmegaVarElim ty' Id)) UniverseTy
                     -- Original problem still persists, but gets simplified!
                    , TypeConstraint ctx (El $ ElEqTy (OmegaVarElim a0' Id) (OmegaVarElim a1' Id) (OmegaVarElim ty' Id)) (ElEqTy a0 a1 ty)
                    ]
                    [(ctx, ty', Right UniverseTy), (ctx, a0', Right (El $ OmegaVarElim ty' Id)), (ctx, a1', Right (El $ OmegaVarElim ty' Id))]
                    []
           )
  unifyElAgainstRigid sig omega ctx el (El x) = assert_total $ idris_crash "unifyElAgainstRigid (El _)"
  unifyElAgainstRigid sig omega ctx el (ContextSubstElim x y) = assert_total $ idris_crash "unifyElAgainstRigid (_(_))"
  unifyElAgainstRigid sig omega ctx el (SignatureSubstElim x y) = assert_total $ idris_crash "unifyElAgainstRigid (_(_))"
  unifyElAgainstRigid sig omega ctx el (OmegaVarElim str x) = assert_total $ idris_crash "unifyElAgainstRigid (Ωᵢ)"

  ||| Σ Ω Γ ⊦ A₀ ~ A₁ type
  ||| A₀ and A₁ are head-neutral w.r.t. substitution.
  public export
  unifyTypeMetaNu : Signature -> Omega -> Context -> Typ -> Typ -> UnifyM Result
  unifyTypeMetaNu sig cs ctx a@(OmegaVarElim k0 sigma0) b@(OmegaVarElim k1 sigma1) = St.do
    let Just entry0 = lookup k0 cs
         | _ => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim(1))"
    let Just entry1 = lookup k1 cs
         | _ => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim(2))"
    case (entry0, entry1) of
      -- Both sides are holes, try solving for each side.
      (MetaType hctx0 SolveByUnification, MetaType hctx1 SolveByUnification) => St.do
         case !(liftEvalM $ trySolveType sig cs ctx k0 hctx0 sigma0 b) of
           Success cs [] sols => pure (Success cs [] sols)
           Success cs (_ :: _) sols => assert_total $ idris_crash "unifyTypeMetaNu(Meta, Meta)"
           Stuck _ => liftEvalM $ trySolveType sig cs ctx k1 hctx1 sigma1 a
           Disunifier dis => pure (Disunifier dis)
      -- One side is a hole
      (MetaType hctx0 SolveByUnification, _) => St.do
        liftEvalM $ trySolveType sig cs ctx k0 hctx0 sigma0 b
      -- One side is a hole
      (_, MetaType hctx1 SolveByUnification) => St.do
        liftEvalM $ trySolveType sig cs ctx k1 hctx1 sigma1 a
      (e, _) => St.do
        case (!(liftEvalM $ isRigid sig cs a) && !(liftEvalM $ isRigid sig cs b)) of
          True =>
            case (k0 == k1) of
              False => pure (Disunifier "χᵢ vs χⱼ, where i ≠ j")
              True =>
                case e of
                  LetType target {} => pure (Success [SubstContextConstraint sigma0 sigma1 ctx target] [] [])
                  _ => assert_total $ idris_crash "unifyTypeMetaNu(SignatureVarElim, SignatureVarElim)(1)"
          False => pure (Stuck "χᵢ vs χⱼ, where i ≠ j, flex")
  unifyTypeMetaNu sig cs ctx a@(OmegaVarElim k sigma) b = St.do
    case (!(liftEvalM $ isRigid sig cs a), !(liftEvalM $ isRigid sig cs b)) of
      (True, True) => pure (Disunifier "rigid χᵢ vs something else rigid")
      (True, False) => pure (Stuck "rigid χᵢ vs something else flex")
      (False, _) => M.do
       let Just entry = lookup k cs
            | _ => assert_total $ idris_crash "unifyTypeNu(SignatureVarElim(3))"
       case entry of
         -- We've got a hole, try solving it
         MetaType hctx SolveByUnification => liftEvalM $ trySolveType sig cs ctx k hctx sigma b
         MetaType hctx SolveByElaboration => pure (Stuck "?(solve by elaboration) vs something else rigid")
         MetaType hctx NoSolve => pure (Stuck "?(no solve) vs something else rigid")
         MetaElem hctx _ _ => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(7)"
         LetElem {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(2)"
         LetType {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(3)"
         TypeConstraint {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(4)"
         ElemConstraint {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(5)"
         SubstContextConstraint {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(6)"
  unifyTypeMetaNu sig cs ctx a b@(OmegaVarElim k sigma) = St.do
    case (!(liftEvalM $ isRigid sig cs a), !(liftEvalM $ isRigid sig cs b))  of
      (True, True) => pure (Disunifier "rigid χᵢ vs something else rigid")
      (False, True) => pure (Stuck "rigid χᵢ vs something else flex")
      (_, False) => M.do
       let Just entry = lookup k cs
            | _ => assert_total $ idris_crash "unifyTypeMetaNu(SignatureVarElim(3))"
       case entry of
         -- We've got a hole, try solving it
         MetaType hctx SolveByUnification => liftEvalM $ trySolveType sig cs ctx k hctx sigma a
         MetaType hctx SolveByElaboration => pure (Stuck "?(solve by elaboration) vs something else rigid")
         MetaType hctx NoSolve => pure (Stuck "?(no solve) vs something else rigid")
         -- This is possible, when the type is 𝕌
         MetaElem hctx _ _ => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(7)"
         LetElem {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(2)"
         LetType {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(3)"
         TypeConstraint {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(4)"
         ElemConstraint {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(5)"
         SubstContextConstraint {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(6)"
  unifyTypeMetaNu sig cs ctx a b = pure (Stuck "unifyTypeMetaNu rule doesn't apply")

  ||| Σ Ω Γ ⊦ A₀ ~ A₁ type
  ||| A₀ and A₁ are head-neutral w.r.t. substitution.
  public export
  unifyTypeElimNu : Signature -> Omega -> Context -> Typ -> Typ -> UnifyM Result
  unifyTypeElimNu sig cs ctx (El a0) (El a1) = St.do
    pure (Success [ElemConstraint ctx a0 a1 UniverseTy] [] [])
    {- case !(liftEvalM $ isRigid sig cs a0) || !(liftEvalM $ isRigid sig cs a1) of
      True => pure (Success [ElemConstraint ctx a0 a1 UniverseTy] [] [])
      False => pure (Stuck "El a₀ vs El a₁ where a₀ doesn't convert with a₁, both are flex") -}
  unifyTypeElimNu sig cs ctx (El el) other = St.do
    case !(liftEvalM $ isRigid sig cs other) of
      True => unifyElAgainstRigid sig cs ctx el other
      False => pure (Stuck "El _ vs something else flex")
  unifyTypeElimNu sig cs ctx other (El el) = St.do
    case !(liftEvalM $ isRigid sig cs other) of
      True => unifyElAgainstRigid sig cs ctx el other
      False => pure (Stuck "El _ vs something else flex")
  unifyTypeElimNu sig cs ctx a b = pure (Stuck "unifyTypeElimNu rule doesn't apply")

  ||| Σ Ω Γ ⊦ A₀ ~ A₁ type
  ||| A₀ and A₁ are head-neutral w.r.t. substitution.
  public export
  unifyTypeIntroNu : Signature -> Omega -> Context -> Typ -> Typ -> UnifyM Result
  unifyTypeIntroNu sig cs ctx (PiTy x0 dom0 cod0) (PiTy x1 dom1 cod1) = St.do
    pure (Success [ TypeConstraint ctx dom0 dom1
                    , TypeConstraint (ctx :< (x0, dom0)) cod0 cod1
                    ]
                    []
                    []
           )
  unifyTypeIntroNu sig cs ctx (ImplicitPiTy x0 dom0 cod0) (ImplicitPiTy x1 dom1 cod1) = St.do
    pure (Success [ TypeConstraint ctx dom0 dom1
                    , TypeConstraint (ctx :< (x0, dom0)) cod0 cod1
                    ]
                    []
                    []
           )
  unifyTypeIntroNu sig cs ctx (SigmaTy x0 dom0 cod0) (SigmaTy x1 dom1 cod1) = St.do
    pure (Success [ TypeConstraint ctx dom0 dom1
                    , TypeConstraint (ctx :< (x0, dom0)) cod0 cod1
                    ]
                    []
                    []
           )
  unifyTypeIntroNu sig cs ctx UniverseTy UniverseTy =
    St.pure (Success [] [] [])
  unifyTypeIntroNu sig cs ctx NatTy NatTy = St.pure (Success [] [] [])
  unifyTypeIntroNu sig cs ctx ZeroTy ZeroTy = St.pure (Success [] [] [])
  unifyTypeIntroNu sig cs ctx OneTy OneTy = St.pure (Success [] [] [])
  unifyTypeIntroNu sig cs ctx (ContextSubstElim x y) b = assert_total $ idris_crash "unifyTypeIntroNu(ContextSubstElim)"
  unifyTypeIntroNu sig cs ctx (SignatureSubstElim x y) b = assert_total $ idris_crash "unifyTypeIntroNu(SignatureSubstElim)"
  unifyTypeIntroNu sig cs ctx (TyEqTy p0 q0) (TyEqTy p1 q1) = St.do
    pure (Success [  TypeConstraint ctx p0 p1,
                       TypeConstraint ctx q0 q1] [] [])
  unifyTypeIntroNu sig cs ctx (ElEqTy p0 q0 ty0) (ElEqTy p1 q1 ty1) = St.do
    pure (Success [  TypeConstraint ctx ty0 ty1,
                       ElemConstraint ctx p0 p1 ty0,
                       ElemConstraint ctx q0 q1 ty0] [] [])
  unifyTypeIntroNu sig cs ctx _ _ = St.pure (Stuck "unifyTypeIntroNu rule doesn't apply")

  public export
  unifyType : Signature -> Omega -> Context -> Typ -> Typ -> UnifyM Result
  unifyType sig cs ctx a b = St.do
    a <- liftEvalM $ openEval sig cs a
    b <- liftEvalM $ openEval sig cs b
    unifyTypeMetaNu sig cs ctx a b <||> unifyTypeElimNu sig cs ctx a b <||> unifyTypeIntroNu sig cs ctx a b

namespace SubstContextNF
  public export
  unify : Signature -> Omega -> SubstContextNF -> SubstContextNF -> Context -> Context -> UnifyM Result
  unify sig cs Terminal b source target = pure (Success [] [] [])
  unify sig cs (WkN k) Terminal source target = pure (Success [] [] [])
  unify sig cs (WkN k) (WkN j) source target =
    case (k == j) of
      True => pure (Success [] [] [])
      False => pure (Disunifier "↑ⁱ vs iᵏ where i ≠ k")
  unify sig cs (WkN k) (Ext sigma t) source (target :< (x, ty)) =
    pure (Success [  SubstContextConstraint sigma (WkN (S k)) source target,
                       ElemConstraint source t (ContextVarElim k) (ContextSubstElim ty sigma)] [] [])
  unify sig cs (WkN k) (Ext sigma t) source target = pure (Stuck "↑ⁿ vs (_, _) where the target context is not an extension")
  unify sig cs (Ext x y) Terminal source target = pure (Success [] [] [])
  unify sig cs (Ext sigma t) (WkN k) source (target :< (x, ty)) =
    pure (Success [  SubstContextConstraint sigma (WkN (S k)) source target,
                       ElemConstraint source t (ContextVarElim k) (ContextSubstElim ty sigma)] [] [])
  unify sig cs (Ext sigma t) (WkN k) source target = pure (Stuck "↑ⁿ vs (_, _) where the target context is not an extension")
  unify sig cs (Ext sigma p) (Ext tau q) source (target :< (x, ty)) =
    pure (Success [  SubstContextConstraint sigma tau source target,
                       ElemConstraint source p q (ContextSubstElim ty sigma)] [] [])
  unify sig cs (Ext sigma p) (Ext tau q) source target = pure (Stuck "(_, _) vs (_, _) where the target context is not an extension")

namespace SubstContext
  -- Ext σ t ~ Ext σ' t' : Γ ⇒ Δ (x : A) <=> (σ = σ' : Γ ⇒ Δ) ^ (Γ ⊦ t ~ t' : A(σ))
  -- Terminal ~ _ <=> 𝟙
  -- Ext σ t ~ Wk k : Γ ⇒ Δ (x : A) <=> (σ ~ Wk (S k) : Γ ⇒ Δ) ^ (Γ ⊦ t ~ Var k : A(σ))
  -- (Wk k ~ Wk n : _) <=> k = n
  public export
  unifySubstContext : Signature -> Omega -> SubstContext -> SubstContext -> Context -> Context -> UnifyM Result
  unifySubstContext sig cs a b source target = unify sig cs (eval a) (eval b) source target

namespace ConstraintEntry
  public export
  unify : Signature -> Omega -> ConstraintEntry -> UnifyM Result
  unify sig cs (TypeConstraint ctx a b) = St.do
    case !(liftEvalM $ conv sig cs a b) of
      True => pure (Success [] [] [])
      False => unifyType sig cs ctx a b
  unify sig cs (ElemConstraint ctx a b ty) = St.do
    case !(liftEvalM $ conv sig cs a b) of
      True => pure (Success [] [] [])
      False => unifyElem sig cs ctx a b ty
  unify sig cs (SubstContextConstraint sigma tau source target) = St.do
    case !(liftEvalM $ conv sig cs sigma tau) of
      True => pure (Success [] [] [])
      False => unifySubstContext sig cs sigma tau source target

namespace Typ
  public export
  instantiate : Omega -> OmegaName -> Typ -> Omega
  instantiate omega idx rhs =
    case (lookup idx omega) of
      Just (MetaType ctx SolveByUnification) => insert (idx, LetType ctx rhs) omega
      _ => assert_total $ idris_crash "instantiate"

namespace Elem
  public export
  instantiate : Omega -> OmegaName -> Elem -> Omega
  instantiate omega idx rhs =
    case (lookup idx omega) of
      Just (MetaElem ctx ty SolveByUnification) => insert (idx, LetElem ctx rhs ty) omega
      _ => assert_total $ idris_crash "instantiate"

public export
instantiateN : Omega -> List (OmegaName, Either Typ Elem) -> Omega
instantiateN sig [] = sig
instantiateN sig ((idx, Left rhs) :: rest) = instantiateN (instantiate sig idx rhs) rest
instantiateN sig ((idx, Right rhs) :: rest) = instantiateN (instantiate sig idx rhs) rest

public export
addConstraint : Omega -> ConstraintEntry -> UnifyM Omega
addConstraint omega e = St.do
  x <- nextOmegaName
  pure $ insert (x, toOmegaEntry e) omega

namespace Named
  ||| The name must be unique!
  public export
  newTypeMeta : Omega -> Context -> OmegaName -> MetaKind -> UnifyM Omega
  newTypeMeta omega ctx n k = St.do
    case lookup n omega of
      Just _ => assert_total $ idris_crash "newTypeMeta, name already exists: \{n}"
      Nothing => pure (insert (n, MetaType ctx k) omega)

  ||| The name must be unique!
  public export
  newElemMeta : Omega -> Context -> OmegaName -> Typ -> MetaKind -> UnifyM Omega
  newElemMeta omega ctx n ty k = St.do
    case lookup n omega of
      Just _ => assert_total $ idris_crash "newElemMeta, name already exists: \{n}"
      Nothing => pure (insert (n, MetaElem ctx ty k) omega)

namespace Nameless
  public export
  newTypeMeta : Omega -> Context -> MetaKind -> UnifyM (Omega, OmegaName)
  newTypeMeta omega ctx k = St.do
    n <- nextOmegaName
    pure (!(Named.newTypeMeta omega ctx n k), n)

  public export
  newElemMeta : Omega -> Context -> Typ -> MetaKind -> UnifyM (Omega, OmegaName)
  newElemMeta omega ctx ty k = St.do
    n <- nextOmegaName
    {- case k of
      SolveByElaboration => print_ Debug STDOUT "Creating new elab-meta: \{n}"
      _ => pure () -}
    pure (!(Named.newElemMeta omega ctx n ty k), n)

public export
addConstraintN : Omega -> List ConstraintEntry -> UnifyM Omega
addConstraintN omega [] = pure omega
addConstraintN omega (e :: es) = addConstraintN !(addConstraint omega e) es

public export
addMetaN : Omega -> List (Context, OmegaName, Either () Typ) -> UnifyM Omega
addMetaN sig [] = pure sig
addMetaN sig ((ctx, idx, Left ()) :: rest) = addMetaN !(Named.newTypeMeta sig ctx idx SolveByUnification) rest
addMetaN sig ((ctx, idx, Right ty) :: rest) = addMetaN !(Named.newElemMeta sig ctx idx ty SolveByUnification) rest

namespace Progress
  ||| The intermediate results of solving a list of constraints (reflects whether at least some progress has been made).
  public export
  data Progress : Type where
    ||| We've made at least one step in the process of solving constraints.
    ||| Ω may contain new instantiations but no new constraints.
    ||| All new constraints are stored in the second argument.
    Success : Omega -> Constraints -> Progress
    ||| We've haven't progressed at all.
    Stuck : String -> Progress
    ||| Ω ≃ ⊥ // The list of constraints is contradictive.
    Disunifier : String -> Progress

namespace MetaProgress
  public export
  data MetaProgress : Type where
    ||| We've made at least one step in the process of solving constraints.
    ||| Ω may contain new instantiations but no new constraints and no new holes.
    ||| All new constraints and holes are stored separately.
    Success : Omega -> List (Context, OmegaName, Typ) -> List ConstraintEntry -> MetaProgress
    ||| We've haven't progressed at all.
    Stuck : String -> MetaProgress

  public export
  prettyProgress : Signature -> Progress.Progress -> PrettyM (Doc Ann)
  prettyProgress sig (Success omega cs) = Reader.do
    pure $
      "Success, sub-problems:"
       <+>
      hardline
       <+>
      !(prettyConstraints sig omega cs)
  prettyProgress sig (Stuck reason) = Reader.do
    pure (pretty "Stuck, reason: \{reason}")
  prettyProgress sig (Disunifier reason) = Reader.do
    pure (pretty "Disunifier, reason: \{reason}")

progressEntry : Signature -> Omega -> ConstraintEntry -> UnifyM Progress
progressEntry sig omega entry = St.do
  {- print_ Debug STDOUT "--------- Unifying ---------"
  print_ Debug STDOUT (renderDocTerm !(liftEvalM $ prettyConstraintEntry sig omega entry)) -}
  let go : Signature -> Omega -> ConstraintEntry -> UnifyM Progress
      go sig cs e = St.do
        case !(unify sig cs e) of
          Success new metas is => St.do
            let metaToOmegaEntry : (Context, OmegaName, Either () Typ) -> (VarName, OmegaEntry)
                metaToOmegaEntry (ctx, idx, Left ()) = (idx, MetaType ctx SolveByUnification)
                metaToOmegaEntry (ctx, idx, Right ty) = (idx, MetaElem ctx ty SolveByUnification)
            let letToOmegaEntry : (OmegaName, Either Typ Elem) -> (VarName, OmegaEntry)
                letToOmegaEntry (idx, Left ty) =
                  case (lookup idx omega) of
                    Just (MetaType ctx _) => (idx, LetType ctx ty)
                    _ => assert_total $ idris_crash "letToOmegaEntry"
                letToOmegaEntry (idx, Right rhs) =
                  case (lookup idx omega) of
                    Just (MetaElem ctx ty _) => (idx, LetElem ctx rhs ty)
                    _ => assert_total $ idris_crash "letToOmegaEntry"

            {- print_ Debug STDOUT "New metas:"
            print_ Debug STDOUT (renderDocTerm !(liftEvalM $ prettyOmega' sig omega (map metaToOmegaEntry metas)))
            print_ Debug STDOUT "Solutions:"
            print_ Debug STDOUT (renderDocTerm !(liftEvalM $ prettyOmega' sig omega (map letToOmegaEntry is))) -}
            let cs = instantiateN cs is
            cs <- addMetaN cs metas
            pure (Success cs (cast new))
          Stuck str => St.pure (Stuck str)
          Disunifier str => St.pure (Disunifier str)
  progress <- go sig omega entry
  {- print_ Debug STDOUT "Progress:"
  print_ Debug STDOUT (renderDocTerm !(liftEvalM $ prettyProgress sig progress))
  print_ Debug STDOUT "-------------------------------" -}
  pure progress

progressElemMetaNu : Signature -> Omega -> Context -> OmegaName -> Typ -> UnifyM MetaProgress
progressElemMetaNu sig omega ctx idx ZeroTy = St.pure (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx OneTy = St.pure (Success (insert (idx, LetElem ctx OneVal OneTy) omega) [] [])
progressElemMetaNu sig omega ctx idx UniverseTy = St.pure (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx NatTy = St.pure (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx ty@(PiTy x dom cod) = St.do
  f <- nextOmegaName
  pure (Success (insert (idx, LetElem ctx (PiVal x dom cod (OmegaVarElim f Id)) ty) omega) [(ctx :< (x, dom), f, cod)] [])
progressElemMetaNu sig omega ctx idx ty@(ImplicitPiTy x dom cod) = St.do
  f <- nextOmegaName
  pure (Success (insert (idx, LetElem ctx (ImplicitPiVal x dom cod (OmegaVarElim f Id)) ty) omega) [(ctx :< (x, dom), f, cod)] [])
progressElemMetaNu sig omega ctx idx ty@(SigmaTy x dom cod) = St.do
  a <- nextOmegaName
  b <- nextOmegaName
  pure (Success
            (insert (idx, LetElem ctx (SigmaVal x dom cod (OmegaVarElim a Id) (OmegaVarElim b Id)) ty) omega)
            [ (ctx, a, dom), (ctx, b, (ContextSubstElim cod (Ext Id (OmegaVarElim a Id))))] []
         )
progressElemMetaNu sig omega ctx idx (TyEqTy a b) = St.pure (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx (ElEqTy x y z) = St.pure (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx (El x) = St.pure (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx (ContextSubstElim x y) = assert_total $ idris_crash "progressElemMetaNu(ContextSubstElim)"
progressElemMetaNu sig omega ctx idx (SignatureSubstElim x y) = assert_total $ idris_crash "progressElemMetaNu(SignatureSubstElim)"
progressElemMetaNu sig omega ctx idx (OmegaVarElim str x) = St.pure (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx (SignatureVarElim str x) = St.pure (Stuck "No canonical Elem exists")

progressMeta : Signature -> Omega -> OmegaName -> MetaBindingEntry -> UnifyM MetaProgress
progressMeta sig omega idx (MetaType ctx _) = St.pure (Stuck "Skipping Type meta")
progressMeta sig omega idx (MetaElem ctx ty NoSolve) = St.pure (Stuck "Skipping NoSolve Elem meta")
progressMeta sig omega idx (MetaElem ctx ty SolveByElaboration) = St.pure (Stuck "Skipping SolveByElaboration Elem meta")
progressMeta sig omega idx (MetaElem ctx ty SolveByUnification) = progressElemMetaNu sig omega ctx idx !(liftEvalM $ openEval sig omega ty)

namespace Progress2
  ||| The intermediate results of solving a list of constraints (reflects whether at least some progress has been made).
  public export
  data Progress2 : Type where
    ||| We've traversed the list of pending constraints once.
    ||| The new Ω may contain new instantiations and new constraints.
    Success : Omega -> Progress2
    ||| We haven't progressed at all.
    Stuck : List (ConstraintEntry, String) -> Progress2
    ||| Ω ≃ ⊥ // The list of constraints is contradictive.
    Disunifier : ConstraintEntry -> String -> Progress2

namespace HoleProgress2
  ||| The intermediate results of solving a list of constraints (reflects whether at least some progress has been made).
  public export
  data MetaProgress2 : Type where
    ||| We've traversed the list of pending holes once.
    ||| The new Ω may contain new instantiations, new constraints and new holes.
    Success : Omega -> MetaProgress2
    ||| We haven't progressed at all.
    Stuck : MetaProgress2

||| Try canonically instantiating metas in the list by passing through it once.
progressMetas : Signature
             -> (omega : Omega)
             -> List (OmegaName, MetaBindingEntry)
             -> Bool
             -> UnifyM MetaProgress2
progressMetas sig omega [] True = St.pure (Success omega)
progressMetas sig omega [] False = St.pure Stuck
progressMetas sig omega ((idx, binding) :: rest) b = St.do
  case !(progressMeta sig omega idx binding) of
    Success omega newBindings newConstraints => St.do
      omega <- addMetaN omega (newBindings <&> (\(ctx, idx, ty) => (ctx, idx, Right ty)))
      omega <- addConstraintN omega newConstraints
      progressMetas sig omega rest True
    Stuck reason => progressMetas sig omega rest b

||| Try solving the constraints in the list by passing through it once.
progressEntries : Signature
               -> (omega : Omega)
               -> List ConstraintEntry
               -> Bool
               -> UnifyM Progress2
progressEntries sig cs [] False = St.pure (Stuck [])
progressEntries sig cs [] True = St.pure (Success cs)
progressEntries sig cs (e :: es) progressMade = St.do
  case !(progressEntry sig cs e) of
    Success cs' new => progressEntries sig cs' (new <>> es) True
    Stuck str => St.do
      case !(progressEntries sig !(addConstraint cs e) es progressMade) of
        Stuck list => St.pure (Stuck ((e, str) :: list))
        Success omega => St.pure (Success omega)
        Disunifier e s => St.pure (Disunifier e s)
    Disunifier str => St.pure (Disunifier e str)

namespace Fixpoint
  ||| The end-product of solving a list of constraints
  public export
  data Fixpoint : Type where
    ||| At least some progress has been made but nothing else can be done.
    Success : Omega -> Fixpoint
    ||| No progress has been made at all.
    Stuck : List (ConstraintEntry, String) -> Fixpoint
    ||| Ω ≃ ⊥ // The list of constraints is contradictive.
    Disunifier : ConstraintEntry -> String -> Fixpoint

||| Extract all constraints from Ω.
getConstraints : Omega -> List ConstraintEntry
getConstraints omega = mapMaybe (mbConstraintEntry . snd) (List.inorder omega)

namespace Omega
  ||| Extract meta bindings from Ω
  public export
  getMetaBindings : Omega -> List (OmegaName, MetaBindingEntry)
  getMetaBindings omega = mapMaybe doFilter (List.inorder omega)
    where
     doFilter : (OmegaName, OmegaEntry) -> Maybe (OmegaName, MetaBindingEntry)
     doFilter (idx, e) = Prelude.do
       e <- mbMetaBindingEntry e
       pure (idx, e)

namespace BindingEntry
  ||| Extract meta bindings from Ω
  public export
  getMetaBindings : List (OmegaName, BindingEntry) -> List (OmegaName, MetaBindingEntry)
  getMetaBindings bindings = mapMaybe doFilter bindings
    where
     doFilter : (OmegaName, BindingEntry) -> Maybe (OmegaName, MetaBindingEntry)
     doFilter (idx, e) = Prelude.do
       e <- mbMetaBindingEntry e
       pure (idx, e)

||| Extract bindings from Ω
getBindings : Omega -> List (OmegaName, BindingEntry)
getBindings omega = mapMaybe doFilter (List.inorder omega)
  where
   doFilter : (OmegaName, OmegaEntry) -> Maybe (OmegaName, BindingEntry)
   doFilter (idx, e) = Prelude.do
     e <- mbBindingEntry e
     pure (idx, e)

public export
containsNamedHolesOnly : Omega -> Bool
containsNamedHolesOnly omega = H (map snd (List.inorder omega))
 where
  H : List OmegaEntry -> Bool
  H [] = True
  H (LetElem {} :: es) = H es
  H (LetType {} :: es) = H es
  H (MetaType ctx NoSolve :: es) = H es
  H (MetaType ctx SolveByElaboration :: es) = H es
  H (MetaType ctx SolveByUnification :: es) = False
  H (MetaElem ctx ty NoSolve :: es) = H es
  H (MetaElem ctx ty SolveByElaboration :: es) = H es
  H (MetaElem ctx ty SolveByUnification :: es) = False
  H (TypeConstraint {} :: es) = False
  H (ElemConstraint {} :: es) = False
  H (SubstContextConstraint {} :: es) = False

||| Try solving the constraints in the list until either no constraints are left or each and every one is stuck.
||| Here Ω is split into bindings (metas and lets) and constraints (equations)
progressEntriesFixpoint : Signature -> List (OmegaName, BindingEntry) -> List ConstraintEntry -> Bool -> UnifyM Fixpoint
progressEntriesFixpoint sig bindings constraints progress = St.do
  case !(progressEntries sig (toOmega bindings) constraints False) of
    Stuck list =>
      case progress of
        True => St.pure (Success !(addConstraintN (toOmega bindings) constraints))
        False => St.do
          case !(progressMetas sig (toOmega bindings) (getMetaBindings bindings) False) of
            Success omega => progressEntriesFixpoint sig (getBindings omega) (getConstraints omega ++ constraints) True
            Stuck => St.pure (Stuck list)
    Disunifier e str => St.pure (Disunifier e str)
    Success omega => progressEntriesFixpoint sig (getBindings omega) (getConstraints omega) True

public export
solve : Signature -> Omega -> UnifyM Fixpoint
solve sig omega = progressEntriesFixpoint sig (getBindings omega) (getConstraints omega) False
