module Nova.Core.Unification

import Data.List
import Data.SnocList
import Data.Util
import Data.Maybe
import Data.AVL
import Data.Fin
import Data.Location

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Conversion
import Nova.Core.Context
import Nova.Core.Evaluation
import Nova.Core.Language
import Nova.Core.Monad
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
UnifyM = JustAMonad.M CriticalError UnifySt

namespace UnifyM
  public export
  liftM : M a -> UnifyM a
  liftM f = M.do
    st <- get
    mapState (const st) (const ()) f

  namespace Maybe
    public export
    liftM : M a -> UnifyM (Maybe a)
    liftM f = M.do
      UnifyM.liftM f <&> Just

public export
nextOmegaName : UnifyM OmegaName
nextOmegaName = M.do
  MkUnifySt idx <- get
  set (MkUnifySt (S idx))
  return ("?\{show idx}")

public export
nextOmegaIdx : UnifyM Nat
nextOmegaIdx = M.do
  MkUnifySt idx <- get
  set (MkUnifySt (S idx))
  return idx

%hide UnifyM.Maybe.liftM

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
          -> M (Maybe SubstContext)
    invert sig omega sigma Terminal gamma delta xi = MMaybe.do return Terminal
    -- σ : Γ₀ Γ₁ ⇒ Δ
    -- ↑(Γ₁) : Γ₀ Γ₁ ⇒ Γ₀
    -- ? : Δ ⇒ Γ₀ such that ? ∘ σ ~ ↑(Γ₁)
    --
    -- in that case ↑ᵏ = ·
    invert sig omega sigma (WkN k) gamma delta [<] = MMaybe.do return Terminal
    -- in that case ↑ᵏ = (↑ᵏ⁺¹, k)
    invert sig omega sigma (WkN k) gamma delta xi@(_ :< _) =
      SubstContextNF.invert sig omega sigma (Ext (WkN (S k)) (ContextVarElim k)) gamma delta xi
    invert sig omega sigma (Ext tau t) gamma delta (xi :< _) = MMaybe.do
      tau' <- invert sig omega sigma tau gamma delta xi
      t' <- invert sig omega gamma delta sigma t
      return (Ext tau' t')
    invert sig omega sigma (Ext tau t) gamma delta _ = MMaybe.do
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
          -> M (Maybe SubstContext)
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
            -> M (Maybe Typ)
    invertNu sig omega ctx delta sigma (PiTy x dom cod) = MMaybe.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      return (PiTy x dom' cod')
    invertNu sig omega ctx delta sigma (ImplicitPiTy x dom cod) = MMaybe.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      return (ImplicitPiTy x dom' cod')
    invertNu sig omega ctx delta sigma (SigmaTy x dom cod) = MMaybe.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      return (SigmaTy x dom' cod')
    invertNu sig omega ctx delta sigma NatTy = MMaybe.do return NatTy
    invertNu sig omega ctx delta sigma ZeroTy = MMaybe.do return ZeroTy
    invertNu sig omega ctx delta sigma OneTy = MMaybe.do return OneTy
    invertNu sig omega ctx delta sigma UniverseTy = MMaybe.do return UniverseTy
    invertNu sig omega ctx delta sigma (El a) = MMaybe.do
      a' <- invert sig omega ctx delta sigma a
      return (El a')
    invertNu sig omega ctx delta sigma (ContextSubstElim x y) = assert_total $ idris_crash "invertNu(ContextSubstElim)"
    invertNu sig omega ctx delta sigma (SignatureSubstElim x y) = assert_total $ idris_crash "invertNu(SignatureSubstElim)"
    invertNu sig omega ctx delta sigma (OmegaVarElim k tau) = MMaybe.do
      tau' <- invert sig omega sigma tau ctx delta getOmega
      return (OmegaVarElim k tau')
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
    invertNu sig omega ctx delta sigma (TyEqTy a b) = MMaybe.do
      a <- invert sig omega ctx delta sigma a
      b <- invert sig omega ctx delta sigma b
      return (TyEqTy a b)
    invertNu sig omega ctx delta sigma (ElEqTy a b ty) = MMaybe.do
      a <- invert sig omega ctx delta sigma a
      b <- invert sig omega ctx delta sigma b
      ty <- invert sig omega ctx delta sigma ty
      return (ElEqTy a b ty)
    invertNu sig omega ctx delta sigma (SignatureVarElim k tau) = MMaybe.do
      tau' <- invert sig omega sigma tau ctx delta getCtx
      return (SignatureVarElim k tau')
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
    invert : Signature -> Omega -> Context -> Context -> SubstContext -> Typ -> M (Maybe Typ)
    invert sig omega ctx delta sigma tm = invertNu sig omega ctx delta sigma !(liftM $ openEval sig omega tm)

  namespace Elem
    -- Substitution x̄ can only be a mixture of permutation and deletition.
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
            -> M (Maybe Elem)
    invertNu sig omega ctx delta sigma (PiTy x dom cod) = MMaybe.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, El dom)) (delta :< (x, El dom')) (Under sigma) cod
      return (PiTy x dom' cod')
    invertNu sig omega ctx delta sigma (ImplicitPiTy x dom cod) = MMaybe.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, El dom)) (delta :< (x, El dom')) (Under sigma) cod
      return (ImplicitPiTy x dom' cod')
    invertNu sig omega ctx delta sigma (SigmaTy x dom cod) = MMaybe.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, El dom)) (delta :< (x, El dom')) (Under sigma) cod
      return (SigmaTy x dom' cod')
    invertNu sig omega ctx delta sigma (PiVal x dom cod f) = MMaybe.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      f' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) f
      return (PiVal x dom' cod' f')
    invertNu sig omega ctx delta sigma (ImplicitPiVal x dom cod f) = MMaybe.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      f' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) f
      return (ImplicitPiVal x dom' cod' f')
    invertNu sig omega ctx delta sigma (SigmaVal x dom cod p q) = MMaybe.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      p' <- invert sig omega ctx delta sigma p
      q' <- invert sig omega ctx delta sigma q
      return (SigmaVal x dom' cod' p' q')
    invertNu sig omega ctx delta sigma (PiElim f x dom cod e) = MMaybe.do
      f' <- invert sig omega ctx delta sigma f
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      e' <- invert sig omega ctx delta sigma e
      return (PiElim f' x dom' cod' e')
    invertNu sig omega ctx delta sigma (ImplicitPiElim f x dom cod e) = MMaybe.do
      f' <- invert sig omega ctx delta sigma f
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      e' <- invert sig omega ctx delta sigma e
      return (ImplicitPiElim f' x dom' cod' e')
    invertNu sig omega ctx delta sigma (SigmaElim1 f x dom cod) = MMaybe.do
      f' <- invert sig omega ctx delta sigma f
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      return (SigmaElim1 f' x dom' cod')
    invertNu sig omega ctx delta sigma (SigmaElim2 f x dom cod) = MMaybe.do
      f' <- invert sig omega ctx delta sigma f
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (ctx :< (x, dom)) (delta :< (x, dom')) (Under sigma) cod
      return (SigmaElim2 f' x dom' cod')
    invertNu sig omega ctx delta sigma NatVal0 = MMaybe.do return NatVal0
    invertNu sig omega ctx delta sigma (NatVal1 t) = MMaybe.do
      t <- invert sig omega ctx delta sigma t
      return (NatVal1 t)
    invertNu sig omega ctx delta sigma NatTy = MMaybe.do return NatTy
    invertNu sig omega ctx delta sigma ZeroTy = MMaybe.do return ZeroTy
    invertNu sig omega ctx delta sigma OneTy = MMaybe.do return OneTy
    invertNu sig omega ctx delta sigma OneVal = MMaybe.do return OneVal
    invertNu sig omega ctx delta sigma (ZeroElim ty t) = MMaybe.do
      ty' <- invert sig omega ctx delta sigma ty
      t' <- invert sig omega ctx delta sigma t
      return (ZeroElim ty' t')
    invertNu sig omega ctx delta sigma (NatElim x schema z y h s t) = MMaybe.do
      schema' <- invert sig omega (ctx :< (x, NatTy)) (delta :< (x, NatTy)) (Under sigma) schema
      z' <- invert sig omega ctx delta sigma z
      s' <- invert sig omega (ctx :< (y, NatTy) :< (h, schema)) (delta :< (y, NatTy) :< (h,  schema')) (Under (Under sigma)) s
      t' <- invert sig omega ctx delta sigma t
      return (NatElim x schema' z' y h s' t')
    invertNu sig omega ctx delta sigma (ContextSubstElim x y) = assert_total $ idris_crash "invertNu(ContextSubstElim)"
    invertNu sig omega ctx delta sigma (SignatureSubstElim x y) = assert_total $ idris_crash "invertNu(SignatureSubstElim)"
    invertNu sig omega ctx delta sigma (ContextVarElim k) = MMaybe.do
      index <- go sigma 0
      return (ContextVarElim index)
     where
      mutual
        goNu : SubstContextNF -> Nat -> M (Maybe Nat)
        goNu Terminal index = nothing
        -- ↑ⁱ
        goNu (WkN i) index =
          case k >= i of
            -- We won't find k
            False => nothing
            -- We'll find k
            True => return (index + (k `minus` i))
        -- due to the conditions imposed on σ, t must be a variable up to (~)
        goNu (Ext sigma t) index = MMaybe.do
          case !(liftM $ openEval sig omega t) of
            ContextVarElim i =>
              case (i == k) of
                True => return index
                False => go sigma (S index)
            _ => assert_total $ idris_crash "invertNu(ContextVarElim)"

        go : SubstContext -> Nat -> M (Maybe Nat)
        go sigma index = goNu (eval sigma) index
    -- σ : Γ ⇒ Δ
    -- Γ ⊦ χᵢ (τ : Γ ⇒ Ω)
    -- Δ ⊦ χᵢ (ρ : Δ ⇒ Ω)
    -- Γ ⊦ χᵢ (ρ ∘ σ) = χᵢ τ
    -- that is, we need to find ρ : Δ ⇒ Ω
    -- such that (ρ ∘ σ) ~ τ
    invertNu sig omega ctx delta sigma (SignatureVarElim k tau) = MMaybe.do
      tau' <- invert sig omega sigma tau ctx delta getCtx
      return (SignatureVarElim k tau')
     where
      getCtx : Context
      getCtx =
        case (splitAt sig k) of
          Nothing => assert_total $ idris_crash "invertNu(SignatureVarElim)(1)"
          Just (_, (_, e), rest) =>
            case subst e (WkN $ 1 + length rest) of
             ElemEntry xi {} => xi
             LetElemEntry xi {} => xi
             TypeEntry {} => assert_total $ idris_crash "invertNu(SignatureVarElim)(TypeEntry)"
             LetTypeEntry {} => assert_total $ idris_crash "invertNu(SignatureVarElim)(LetTypeEntry)"
    invertNu sig omega ctx delta sigma (OmegaVarElim k tau) = MMaybe.do
      tau' <- invert sig omega sigma tau ctx delta getOmega
      return (OmegaVarElim k tau')
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
    invertNu sig omega ctx delta sigma (TyEqTy a b) = MMaybe.do
      a <- invert sig omega ctx delta sigma a
      b <- invert sig omega ctx delta sigma b
      return (TyEqTy a b)
    invertNu sig omega ctx delta sigma (ElEqTy a b ty) = MMaybe.do
      a <- invert sig omega ctx delta sigma a
      b <- invert sig omega ctx delta sigma b
      ty <- invert sig omega ctx delta sigma ty
      return (ElEqTy a b ty)
    invertNu sig omega ctx delta sigma (TyEqVal ty) = MMaybe.do
      ty' <- invert sig omega ctx delta sigma ty
      return (TyEqVal ty')
    invertNu sig omega ctx delta sigma (ElEqVal ty e) = MMaybe.do
      ty' <- invert sig omega ctx delta sigma ty
      e' <- invert sig omega ctx delta sigma e
      return (ElEqVal ty' e')

    public export
    invert : Signature -> Omega -> Context -> Context -> SubstContext -> Elem -> M (Maybe Elem)
    invert sig omega ctx delta sigma tm = invertNu sig omega ctx delta sigma !(liftM $ openEval sig omega tm)

mutual
  public export
  preinvertibleNu : Signature -> Omega -> SubstContextNF -> Set Nat -> M Bool
  preinvertibleNu sig omega Terminal vars = return True
  preinvertibleNu sig omega (WkN k) vars = return True
  preinvertibleNu sig omega (Ext sigma t) vars = M.do
    case !(openEval sig omega t) of
      ContextVarElim k => M.do
        return (not $ isElem k vars) `and` preinvertible sig omega sigma (insert k vars)
      _ => return False

  ||| Substitution is pre-invertible if
  ||| it consists of permutations and deletions of variables (up to (~)).
  public export
  preinvertible : Signature -> Omega -> SubstContext -> Set Nat -> M Bool
  preinvertible sig omega sigma vars = preinvertibleNu sig omega (eval sigma) vars

mutual
  namespace SubstContextNF
    public export
    occurs : Signature -> Omega -> SubstContextNF -> OmegaName -> M Bool
    occurs sig omega Terminal k = return False
    occurs sig omega (WkN j) k = return False
    occurs sig omega (Ext sigma t) k = occurs sig omega sigma k `or` occurs sig omega t k

  namespace SubstContext
    public export
    occurs : Signature -> Omega -> SubstContext -> OmegaName -> M Bool
    occurs sig omega sigma k = occurs sig omega (eval sigma) k

  namespace Typ
    public export
    occursNu : Signature -> Omega -> Typ -> OmegaName -> M Bool
    occursNu sig omega (PiTy x dom cod) k =
      occurs sig omega dom k `or` occurs sig omega cod k
    occursNu sig omega (ImplicitPiTy x dom cod) k =
      occurs sig omega dom k `or` occurs sig omega cod k
    occursNu sig omega (SigmaTy x dom cod) k =
      occurs sig omega dom k `or` occurs sig omega cod k
    occursNu sig omega NatTy k = return False
    occursNu sig omega ZeroTy k = return False
    occursNu sig omega OneTy k = return False
    occursNu sig omega UniverseTy k = return False
    occursNu sig omega (El a) k = occurs sig omega a k
    occursNu sig omega (ContextSubstElim x y) k = assert_total $ idris_crash "occursNu(ContextSubstElim)"
    occursNu sig omega (SignatureSubstElim x y) k = assert_total $ idris_crash "occursNu(SignatureSubstElim)"
    occursNu sig omega (OmegaVarElim j sigma) k = return (j == k) `or` occurs sig omega sigma k
    occursNu sig omega (TyEqTy a b) k = occurs sig omega a k `or` occurs sig omega b k
    occursNu sig omega (ElEqTy a b ty) k = occurs sig omega a k `or` occurs sig omega b k `or` occurs sig omega ty k
    occursNu sig omega (SignatureVarElim j sigma) k = occurs sig omega sigma k

    public export
    occurs : Signature -> Omega -> Typ -> OmegaName -> M Bool
    occurs sig omega t k = occursNu sig omega !(openEval sig omega t) k

  namespace Elem
    public export
    occursNu : Signature -> Omega -> Elem -> OmegaName -> M Bool
    occursNu sig omega (PiTy x dom cod) k =
      occurs sig omega dom k `or` occurs sig omega cod k
    occursNu sig omega (ImplicitPiTy x dom cod) k =
      occurs sig omega dom k `or` occurs sig omega cod k
    occursNu sig omega (SigmaTy x dom cod) k =
      occurs sig omega dom k `or` occurs sig omega cod k
    occursNu sig omega (PiVal x dom cod f) k =
      occurs sig omega dom k `or` occurs sig omega cod k `or` occurs sig omega f k
    occursNu sig omega (ImplicitPiVal x dom cod f) k =
      occurs sig omega dom k `or` occurs sig omega cod k `or` occurs sig omega f k
    occursNu sig omega (SigmaVal x a b p q) k =
      occurs sig omega a k `or` occurs sig omega b k `or` occurs sig omega p k `or` occurs sig omega q k
    occursNu sig omega (PiElim f x dom cod e) k =
      occurs sig omega f k `or` occurs sig omega dom k `or` occurs sig omega cod k `or` occurs sig omega e k
    occursNu sig omega (ImplicitPiElim f x dom cod e) k =
      occurs sig omega f k `or` occurs sig omega dom k `or` occurs sig omega cod k `or` occurs sig omega e k
    occursNu sig omega (SigmaElim1 f x dom cod) k =
      occurs sig omega f k `or` occurs sig omega dom k `or` occurs sig omega cod k
    occursNu sig omega (SigmaElim2 f x dom cod) k =
      occurs sig omega f k `or` occurs sig omega dom k `or` occurs sig omega cod k
    occursNu sig omega NatVal0 k = return False
    occursNu sig omega (NatVal1 t) k = occurs sig omega t k
    occursNu sig omega NatTy k = return False
    occursNu sig omega ZeroTy k = return False
    occursNu sig omega OneTy k = return False
    occursNu sig omega OneVal k = return False
    occursNu sig omega (ZeroElim ty t) k =
      occurs sig omega ty k `or` occurs sig omega t k
    occursNu sig omega (NatElim x schema z y h s t) k =
      occurs sig omega schema k `or` occurs sig omega z k `or` occurs sig omega s k `or` occurs sig omega t k
    occursNu sig omega (ContextSubstElim x y) k = assert_total $ idris_crash "occursNu(ContextSubstElim)"
    occursNu sig omega (SignatureSubstElim x y) k = assert_total $ idris_crash "occursNu(SignatureSubstElim)"
    occursNu sig omega (ContextVarElim j) k = return False
    occursNu sig omega (SignatureVarElim j sigma) k = occurs sig omega sigma k
    occursNu sig omega (OmegaVarElim j sigma) k = return (j == k) `or` occurs sig omega sigma k
    occursNu sig omega (TyEqTy a b) k = occurs sig omega a k `or` occurs sig omega b k
    occursNu sig omega (ElEqTy a b ty) k = occurs sig omega a k `or` occurs sig omega b k `or` occurs sig omega ty k
    occursNu sig omega (TyEqVal ty) k =
      occurs sig omega ty k
    occursNu sig omega (ElEqVal ty e) k =
      occurs sig omega ty k `or` occurs sig omega e k

    public export
    occurs : Signature -> Omega -> Elem -> OmegaName -> M Bool
    occurs sig omega t k = occursNu sig omega !(openEval sig omega t) k

||| Σ Ω Γ ⊦ ? σ ~ t : A
public export
trySolveElem : Signature -> Omega -> Context -> OmegaName -> Context -> Typ -> SubstContext -> Elem -> Typ -> M Result
trySolveElem sig omega ctx holeIdx holeCtx holeTy sigma rhs ty = M.do
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
  False <- occurs sig omega rhs holeIdx
    | True => return (Stuck "Occurs check failed") -- TODO: strengthen the check to a disunifier in some cases
  True <- preinvertible sig omega sigma empty
    | False => return (Stuck "Substitution is not invertible")
  Just rhs' <- invert sig omega ctx holeCtx sigma rhs
    | Nothing => return (Stuck "Can't invert RHS")
  return (Success [] [] [(holeIdx, Right rhs')])

||| Σ Ω Γ ⊦ ? σ ~ A type
public export
trySolveType : Signature -> Omega -> Context -> OmegaName -> Context -> SubstContext -> Typ -> M Result
trySolveType sig omega ctx holeIdx holeCtx sigma rhs = M.do
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
  False <- occurs sig omega rhs holeIdx
    | True => return (Stuck "Occurs check failed") -- TODO: strengthen the check to a disunifier in some cases
  True <- preinvertible sig omega sigma empty
    | False => return (Stuck "Substitution is not invertible")
  Just rhs' <- invert sig omega ctx holeCtx sigma rhs
    | Nothing => return (Stuck "Can't invert RHS")
  return (Success [] [] [(holeIdx, Left rhs')])


namespace Elem

  public export
  unifyElemElimNu : Signature -> Omega -> Context -> Elem -> Elem -> UnifyM Result
  unifyElemElimNu sig omega ctx (PiElim f0 x dom cod e0) (PiElim f1 _ _ _ e1) = M.do
    case !(unifyElemElimNu sig omega ctx f0 f1) of
      Success cons metas lets =>
        return (Success (ElemConstraint ctx e0 e1 dom :: cons) metas lets)
      nope => return nope
  unifyElemElimNu sig omega ctx (ImplicitPiElim f0 x dom cod e0) (ImplicitPiElim f1 _ _ _ e1) = M.do
    case !(unifyElemElimNu sig omega ctx f0 f1) of
      Success cons metas lets =>
        return (Success (ElemConstraint ctx e0 e1 dom :: cons) metas lets)
      nope => return nope
  unifyElemElimNu sig omega ctx (SigmaElim1 f0 x dom cod) (SigmaElim1 f1 _ _ _) = M.do
    case !(unifyElemElimNu sig omega ctx f0 f1) of
      Success cons metas lets => return (Success cons metas lets)
      nope => return nope
  unifyElemElimNu sig omega ctx (SigmaElim2 f0 x dom cod) (SigmaElim2 f1 _ _ _) = M.do
    case !(unifyElemElimNu sig omega ctx f0 f1) of
      Success cons metas lets => return (Success cons metas lets)
      nope => return nope
  unifyElemElimNu sig omega ctx (ZeroElim _ t0) (ZeroElim _ t1) = M.do
    case !(unifyElemElimNu sig omega ctx t0 t1) of
      Success cons metas lets => return (Success cons metas lets)
      nope => return nope
  unifyElemElimNu sig omega ctx (NatElim x0 schema0 z0 y0 h0 s0 t0) (NatElim x1 schema1 z1 y1 h1 s1 t1) = M.do
    case !(unifyElemElimNu sig omega ctx t0 t1) of
      Success cons metas lets =>
        return (Success (     TypeConstraint (ctx :< (x0, NatTy)) schema0 schema1
                           :: ElemConstraint ctx z0 z1 (ContextSubstElim schema0 (Ext Id NatVal0))
                           :: ElemConstraint (ctx :< (x0, NatTy) :< (h0, schema0)) s0 s1 (ContextSubstElim schema0 (Ext (Chain Wk Wk) (NatVal1 (NatVal1 (CtxVarN 1)))))
                           :: cons
                        )
                        metas lets
              )
      nope => return nope
      -- ||| Xᵢ(σ)
      -- SignatureVarElim : Nat -> SubstContext -> Elem
      -- ||| Xᵢ(σ)
      -- OmegaVarElim : OmegaName -> SubstContext -> Elem
  unifyElemElimNu sig omega ctx (ContextVarElim x0) (ContextVarElim x1) = M.do
    case (x0 == x1) of
      True => return (Success [] [] [])
      False => return (Disunifier "xᵢ ~ xⱼ where i ≠ j")
  unifyElemElimNu sig omega ctx (SignatureVarElim x0 sigma0) (SignatureVarElim x1 sigma1) = M.do
    case (x0 == x1) of
      True => M.do
        let Just (_, delta) = Index.lookupSignature sig x0 <&> mapSnd getContext
          | Nothing => assert_total $ idris_crash "unifyElemElimNu(1)"
        return (Success [SubstContextConstraint sigma0 sigma1 ctx delta] [] [])
      False => return (Disunifier "xᵢ ~ xⱼ where i ≠ j")
  unifyElemElimNu sig omega ctx _ _ = return (Stuck "Elim rule doesn't apply")

  ||| Σ Ω Γ ⊦ a₀ ~ a₁ : A
  ||| A, a₀, a₁ are head-neutral w.r.t. substitution.
  public export
  unifyElemMetaNu : Signature -> Omega -> Context -> Elem -> Elem -> Typ -> UnifyM Result
  unifyElemMetaNu sig cs ctx a@(OmegaVarElim k0 sigma0) b@(OmegaVarElim k1 sigma1) ty = M.do
    let Just entry0 = lookup k0 cs
         | _ => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim(1))"
    let Just entry1 = lookup k1 cs
         | _ => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim(2))"
    case (entry0, entry1) of
      -- Both sides are holes, try solving for each side.
      (MetaElem hctx0 hty0 SolveByUnification, MetaElem hctx1 hty1 SolveByUnification) =>
         case !(liftM $ trySolveElem sig cs ctx k0 hctx0 hty0 sigma0 b ty) of
           Success cs [] sols => return (Success cs [] sols)
           Success cs (_ :: _) sols => assert_total $ idris_crash "unifyElemNu(Meta, Meta)"
           Stuck _ => liftM $ trySolveElem sig cs ctx k1 hctx1 hty1 sigma1 a ty
           Disunifier dis => return (Disunifier dis)
      -- One side is a hole
      (MetaElem hctx0 hty0 SolveByUnification, _) =>
        liftM $ trySolveElem sig cs ctx k0 hctx0 hty0 sigma0 b ty
      -- One side is a hole
      (_, MetaElem hctx1 hty1 SolveByUnification) =>
        liftM $ trySolveElem sig cs ctx k1 hctx1 hty1 sigma1 a ty
      -- Both sides are rigid
      (e, _) =>
        case (!(liftM $ isRigid sig cs a) && !(liftM $ isRigid sig cs b)) of
          True =>
           case (k0 == k1) of
             False => return (Disunifier "χᵢ vs χⱼ, where i ≠ j")
             True =>
               case e of
                 LetElem target {} => return (Success [SubstContextConstraint sigma0 sigma1 ctx target] [] [])
                 _ => assert_total $ idris_crash "unifyElemMetaNu(SignatureVarElim, SignatureVarElim)(1)"
          False => return (Stuck "χᵢ vs χⱼ, where i ≠ j, flex")
  unifyElemMetaNu sig cs ctx a@(OmegaVarElim k sigma) b ty = M.do
    -- we now that b is rigid here
    case !(liftM $ isRigid sig cs a) of
      True => return (Disunifier "rigid χᵢ vs something else rigid")
      False => M.do
       let Just entry = lookup k cs
            | _ => assert_total $ idris_crash "unifyElemNu(SignatureVarElim(3))"
       case entry of
         -- We've got a hole, try solving it
         MetaElem hctx hty SolveByUnification => liftM $ trySolveElem sig cs ctx k hctx hty sigma b ty
         MetaElem hctx hty SolveByElaboration => return (Stuck "?(solve by elaboration) vs something else rigid")
         MetaElem hctx hty NoSolve => return (Stuck "?(no solve) vs something else rigid")
         MetaType {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(1)"
         LetElem {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(2)"
         LetType {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(3)"
         TypeConstraint {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(4)"
         ElemConstraint {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(5)"
         SubstContextConstraint {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(6)"
  unifyElemMetaNu sig cs ctx a b@(OmegaVarElim k sigma) ty = M.do
    -- we now that a is rigid here
    case !(liftM $ isRigid sig cs b) of
      True => return (Disunifier "rigid χᵢ vs something else rigid")
      False => M.do
       let Just entry = lookup k cs
            | _ => assert_total $ idris_crash "unifyElemMetaNu(SignatureVarElim(3))"
       case entry of
         -- We've got a hole, try solving it
         MetaElem hctx hty SolveByUnification => liftM $ trySolveElem sig cs ctx k hctx hty sigma a ty
         MetaElem hctx hty SolveByElaboration => return (Stuck "?(solve by elaboration) vs something else rigid")
         MetaElem hctx hty NoSolve => return (Stuck "?(no solve) vs something else rigid")
         MetaType {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(1)"
         LetElem {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(2)"
         LetType {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(3)"
         TypeConstraint {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(4)"
         ElemConstraint {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(5)"
         SubstContextConstraint {} => assert_total $ idris_crash "unifyElemMetaNu(OmegaVarElim, _)(6)"
  unifyElemMetaNu sig cs ctx a b ty = return (Stuck "unifyMetaNu rule doesn't apply")

  ||| Σ Ω Γ ⊦ a₀ ~ a₁ : A
  ||| A, a₀, a₁ are head-neutral w.r.t. substitution.
  public export
  unifyElemIntroNu : Signature -> Omega -> Context -> Elem -> Elem -> Typ -> UnifyM Result
  unifyElemIntroNu sig cs ctx (PiTy x0 dom0 cod0) (PiTy x1 dom1 cod1) ty = FailSt.do
    return (Success [ ElemConstraint ctx dom0 dom1 UniverseTy
                    , ElemConstraint (ctx :< (x0, El dom0)) cod0 cod1 UniverseTy
                    ]
                    []
                    []
           )
  unifyElemIntroNu sig cs ctx (ImplicitPiTy x0 dom0 cod0) (ImplicitPiTy x1 dom1 cod1) ty = FailSt.do
    return (Success [ ElemConstraint ctx dom0 dom1 UniverseTy
                    , ElemConstraint (ctx :< (x0, El dom0)) cod0 cod1 UniverseTy
                    ]
                    []
                    []
           )
  unifyElemIntroNu sig cs ctx (SigmaTy x0 dom0 cod0) (SigmaTy x1 dom1 cod1) ty = FailSt.do
    return (Success [ ElemConstraint ctx dom0 dom1 UniverseTy
                    , ElemConstraint (ctx :< (x0, El dom0)) cod0 cod1 UniverseTy
                    ]
                    []
                    []
           )
  unifyElemIntroNu sig cs ctx (PiVal x0 dom0 cod0 f0) (PiVal x1 dom1 cod1 f1) ty = FailSt.do
    return (Success [ElemConstraint (ctx :< (x0, dom0)) f0 f1 cod0]
                    []
                    []
           )
  unifyElemIntroNu sig cs ctx (ImplicitPiVal x0 dom0 cod0 f0) (ImplicitPiVal x1 dom1 cod1 f1) ty = FailSt.do
    return (Success [ElemConstraint (ctx :< (x0, dom0)) f0 f1 cod0]
                    []
                    []
           )
  unifyElemIntroNu sig cs ctx (SigmaVal x a b p0 q0) (SigmaVal _ _ _ p1 q1) _ = FailSt.do
    return (Success [ElemConstraint ctx p0 p1 a, ElemConstraint ctx q0 q1 (ContextSubstElim b (Ext Id p0))]
                    []
                    []
           )
  unifyElemIntroNu sig cs ctx NatVal0 NatVal0 ty =
    return (Success [] [] [])
  unifyElemIntroNu sig cs ctx OneVal OneVal _ =
    return (Success [] [] [])
  unifyElemIntroNu sig cs ctx (NatVal1 t0) (NatVal1 t1) ty = M.do
    return (Success [ ElemConstraint ctx t0 t1 NatTy] [] [])
  unifyElemIntroNu sig cs ctx NatTy NatTy ty = return (Success [] [] [])
  unifyElemIntroNu sig cs ctx ZeroTy ZeroTy ty = return (Success [] [] [])
  unifyElemIntroNu sig cs ctx OneTy OneTy ty = return (Success [] [] [])
  unifyElemIntroNu sig cs ctx (ContextSubstElim x y) b ty = assert_total $ idris_crash "unifyElemIntroNu(ContextSubstElim)"
  unifyElemIntroNu sig cs ctx (SignatureSubstElim x y) b ty = assert_total $ idris_crash "unifyElemIntroNu(SignatureSubstElim)"
  unifyElemIntroNu sig cs ctx (TyEqTy p0 q0) (TyEqTy p1 q1) _ = M.do
    return (Success [  ElemConstraint ctx p0 p1 UniverseTy,
                       ElemConstraint ctx q0 q1 UniverseTy] [] [])
  unifyElemIntroNu sig cs ctx (ElEqTy p0 q0 ty0) (ElEqTy p1 q1 ty1) _ = M.do
    return (Success [  ElemConstraint ctx ty0 ty1 UniverseTy,
                       ElemConstraint ctx p0 p1 (El ty0),
                       ElemConstraint ctx q0 q1 (El ty0)] [] [])
  unifyElemIntroNu sig cs ctx (TyEqVal _) (TyEqVal _) ty = return (Success [] [] [])
  unifyElemIntroNu sig cs ctx (ElEqVal _ _) (ElEqVal _ _) ty = return (Success [] [] [])
  unifyElemIntroNu sig cs ctx a b ty = return (Stuck "UnifyElemIntroNu rule doesn't apply")

  public export
  (<||>) : UnifyM Result -> UnifyM Result -> UnifyM Result
  ma <||> mb = M.do
    case !ma of
      Disunifier err => return (Disunifier err)
      Success a b c => return (Success a b c)
      Stuck _ => mb

  public export
  unifyElem : Signature -> Omega -> Context -> Elem -> Elem -> Typ -> UnifyM Result
  unifyElem sig cs ctx a b ty = M.do
    a <- liftM $ openEval sig cs a
    b <- liftM $ openEval sig cs b
    ty <- liftM $ openEval sig cs ty
    (unifyElemMetaNu sig cs ctx a b ty <||> unifyElemElimNu sig cs ctx a b <||> unifyElemIntroNu sig cs ctx a b ty)

namespace Type'
  ||| Assumes that RHS isn't El, even if rigid.
  public export
  unifyElAgainstRigid : Signature -> Omega -> Context -> Elem -> Typ -> UnifyM Result
  unifyElAgainstRigid sig omega ctx el ZeroTy = M.do
    return (Success [ ElemConstraint ctx el ZeroTy UniverseTy] [] [])
  unifyElAgainstRigid sig omega ctx el OneTy = M.do
    return (Success [ ElemConstraint ctx el OneTy UniverseTy] [] [])
  -- El ? = 𝕌 type <=> ⊥
  unifyElAgainstRigid sig omega ctx el UniverseTy = M.do
    return (Disunifier "El ? = 𝕌 doesn't have solutions for ?")
  unifyElAgainstRigid sig omega ctx el (SignatureVarElim {}) = M.do
    return (Stuck "El ? = Xᵢ σ")
  unifyElAgainstRigid sig omega ctx el NatTy = M.do
    return (Success [ ElemConstraint ctx el NatTy UniverseTy] [] [])
  unifyElAgainstRigid sig omega ctx el (PiTy x dom cod) = M.do
    dom' <- nextOmegaName
    cod' <- nextOmegaName
    return (Success [ ElemConstraint ctx el (PiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id)) UniverseTy
                     -- Original problem still persists, but gets simplified!
                    , TypeConstraint ctx (El (PiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))) (PiTy x dom cod)
                    ]
                    [(ctx, dom', Right UniverseTy), (ctx :< (x, El $ OmegaVarElim dom' Id), cod', Right UniverseTy)]
                    []
           )
  unifyElAgainstRigid sig omega ctx el (ImplicitPiTy x dom cod) = M.do
    dom' <- nextOmegaName
    cod' <- nextOmegaName
    return (Success [ ElemConstraint ctx el (ImplicitPiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id)) UniverseTy
                     -- Original problem still persists, but gets simplified!
                    , TypeConstraint ctx (El (ImplicitPiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))) (ImplicitPiTy x dom cod)
                    ]
                    [(ctx, dom', Right UniverseTy), (ctx :< (x, El $ OmegaVarElim dom' Id), cod', Right UniverseTy)]
                    []
           )
  unifyElAgainstRigid sig omega ctx el (SigmaTy x dom cod) = M.do
    dom' <- nextOmegaName
    cod' <- nextOmegaName
    return (Success [ElemConstraint ctx el (SigmaTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id)) UniverseTy
                     -- Original problem still persists, but gets simplified!
                    , TypeConstraint ctx (El (SigmaTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id))) (SigmaTy x dom cod)
                    ]
                    [(ctx, dom', Right UniverseTy), (ctx :< (x, El $ OmegaVarElim dom' Id), cod', Right UniverseTy)]
                    []
           )
  unifyElAgainstRigid sig omega ctx el (TyEqTy a0 a1) = M.do
    a0' <- nextOmegaName
    a1' <- nextOmegaName
    return (Success [ElemConstraint ctx el (TyEqTy (OmegaVarElim a0' Id) (OmegaVarElim a1' Id)) UniverseTy
                     -- Original problem still persists, but gets simplified!
                    , TypeConstraint ctx (El $ TyEqTy (OmegaVarElim a0' Id) (OmegaVarElim a1' Id)) (TyEqTy a0 a1)
                    ]
                    [(ctx, a0', Right UniverseTy), (ctx, a1', Right UniverseTy)]
                    []
           )
  unifyElAgainstRigid sig omega ctx el (ElEqTy a0 a1 ty) = M.do
    a0' <- nextOmegaName
    a1' <- nextOmegaName
    ty' <- nextOmegaName
    return (Success [ElemConstraint ctx el (ElEqTy (OmegaVarElim a0' Id) (OmegaVarElim a1' Id) (OmegaVarElim ty' Id)) UniverseTy
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
  unifyTypeMetaNu sig cs ctx a@(OmegaVarElim k0 sigma0) b@(OmegaVarElim k1 sigma1) = M.do
    let Just entry0 = lookup k0 cs
         | _ => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim(1))"
    let Just entry1 = lookup k1 cs
         | _ => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim(2))"
    case (entry0, entry1) of
      -- Both sides are holes, try solving for each side.
      (MetaType hctx0 SolveByUnification, MetaType hctx1 SolveByUnification) =>
         case !(liftM $ trySolveType sig cs ctx k0 hctx0 sigma0 b) of
           Success cs [] sols => return (Success cs [] sols)
           Success cs (_ :: _) sols => assert_total $ idris_crash "unifyTypeMetaNu(Meta, Meta)"
           Stuck _ => liftM $ trySolveType sig cs ctx k1 hctx1 sigma1 a
           Disunifier dis => return (Disunifier dis)
      -- One side is a hole
      (MetaType hctx0 SolveByUnification, _) =>
        liftM $ trySolveType sig cs ctx k0 hctx0 sigma0 b
      -- One side is a hole
      (_, MetaType hctx1 SolveByUnification) =>
        liftM $ trySolveType sig cs ctx k1 hctx1 sigma1 a
      (e, _) =>
        case (!(liftM $ isRigid sig cs a) && !(liftM $ isRigid sig cs b)) of
          True =>
            case (k0 == k1) of
              False => return (Disunifier "χᵢ vs χⱼ, where i ≠ j")
              True =>
                case e of
                  LetType target {} => return (Success [SubstContextConstraint sigma0 sigma1 ctx target] [] [])
                  _ => assert_total $ idris_crash "unifyTypeMetaNu(SignatureVarElim, SignatureVarElim)(1)"
          False => return (Stuck "χᵢ vs χⱼ, where i ≠ j, flex")
  unifyTypeMetaNu sig cs ctx a@(OmegaVarElim k sigma) b = M.do
    case (!(liftM $ isRigid sig cs a), !(liftM $ isRigid sig cs b)) of
      (True, True) => return (Disunifier "rigid χᵢ vs something else rigid")
      (True, False) => return (Stuck "rigid χᵢ vs something else flex")
      (False, _) => M.do
       let Just entry = lookup k cs
            | _ => assert_total $ idris_crash "unifyTypeNu(SignatureVarElim(3))"
       case entry of
         -- We've got a hole, try solving it
         MetaType hctx SolveByUnification => liftM $ trySolveType sig cs ctx k hctx sigma b
         MetaType hctx SolveByElaboration => return (Stuck "?(solve by elaboration) vs something else rigid")
         MetaType hctx NoSolve => return (Stuck "?(no solve) vs something else rigid")
         MetaElem hctx _ _ => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(7)"
         LetElem {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(2)"
         LetType {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(3)"
         TypeConstraint {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(4)"
         ElemConstraint {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(5)"
         SubstContextConstraint {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(6)"
  unifyTypeMetaNu sig cs ctx a b@(OmegaVarElim k sigma) = M.do
    case (!(liftM $ isRigid sig cs a), !(liftM $ isRigid sig cs b))  of
      (True, True) => return (Disunifier "rigid χᵢ vs something else rigid")
      (False, True) => return (Stuck "rigid χᵢ vs something else flex")
      (_, False) => M.do
       let Just entry = lookup k cs
            | _ => assert_total $ idris_crash "unifyTypeMetaNu(SignatureVarElim(3))"
       case entry of
         -- We've got a hole, try solving it
         MetaType hctx SolveByUnification => liftM $ trySolveType sig cs ctx k hctx sigma a
         MetaType hctx SolveByElaboration => return (Stuck "?(solve by elaboration) vs something else rigid")
         MetaType hctx NoSolve => return (Stuck "?(no solve) vs something else rigid")
         -- This is possible, when the type is 𝕌
         MetaElem hctx _ _ => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(7)"
         LetElem {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(2)"
         LetType {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(3)"
         TypeConstraint {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(4)"
         ElemConstraint {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(5)"
         SubstContextConstraint {} => assert_total $ idris_crash "unifyTypeMetaNu(OmegaVarElim, _)(6)"
  unifyTypeMetaNu sig cs ctx a b = return (Stuck "unifyTypeMetaNu rule doesn't apply")

  ||| Σ Ω Γ ⊦ A₀ ~ A₁ type
  ||| A₀ and A₁ are head-neutral w.r.t. substitution.
  public export
  unifyTypeElimNu : Signature -> Omega -> Context -> Typ -> Typ -> UnifyM Result
  unifyTypeElimNu sig cs ctx (El a0) (El a1) = M.do
    return (Success [ElemConstraint ctx a0 a1 UniverseTy] [] [])
    {- case !(liftM $ isRigid sig cs a0) || !(liftM $ isRigid sig cs a1) of
      True => return (Success [ElemConstraint ctx a0 a1 UniverseTy] [] [])
      False => return (Stuck "El a₀ vs El a₁ where a₀ doesn't convert with a₁, both are flex") -}
  unifyTypeElimNu sig cs ctx (El el) other = M.do
    case !(liftM $ isRigid sig cs other) of
      True => unifyElAgainstRigid sig cs ctx el other
      False => return (Stuck "El _ vs something else flex")
  unifyTypeElimNu sig cs ctx other (El el) = M.do
    case !(liftM $ isRigid sig cs other) of
      True => unifyElAgainstRigid sig cs ctx el other
      False => return (Stuck "El _ vs something else flex")
  unifyTypeElimNu sig cs ctx a b = return (Stuck "unifyTypeElimNu rule doesn't apply")

  ||| Σ Ω Γ ⊦ A₀ ~ A₁ type
  ||| A₀ and A₁ are head-neutral w.r.t. substitution.
  public export
  unifyTypeIntroNu : Signature -> Omega -> Context -> Typ -> Typ -> UnifyM Result
  unifyTypeIntroNu sig cs ctx (PiTy x0 dom0 cod0) (PiTy x1 dom1 cod1) = FailSt.do
    return (Success [ TypeConstraint ctx dom0 dom1
                    , TypeConstraint (ctx :< (x0, dom0)) cod0 cod1
                    ]
                    []
                    []
           )
  unifyTypeIntroNu sig cs ctx (ImplicitPiTy x0 dom0 cod0) (ImplicitPiTy x1 dom1 cod1) = FailSt.do
    return (Success [ TypeConstraint ctx dom0 dom1
                    , TypeConstraint (ctx :< (x0, dom0)) cod0 cod1
                    ]
                    []
                    []
           )
  unifyTypeIntroNu sig cs ctx (SigmaTy x0 dom0 cod0) (SigmaTy x1 dom1 cod1) = FailSt.do
    return (Success [ TypeConstraint ctx dom0 dom1
                    , TypeConstraint (ctx :< (x0, dom0)) cod0 cod1
                    ]
                    []
                    []
           )
  unifyTypeIntroNu sig cs ctx UniverseTy UniverseTy =
    return (Success [] [] [])
  unifyTypeIntroNu sig cs ctx NatTy NatTy = return (Success [] [] [])
  unifyTypeIntroNu sig cs ctx ZeroTy ZeroTy = return (Success [] [] [])
  unifyTypeIntroNu sig cs ctx OneTy OneTy = return (Success [] [] [])
  unifyTypeIntroNu sig cs ctx (ContextSubstElim x y) b = assert_total $ idris_crash "unifyTypeIntroNu(ContextSubstElim)"
  unifyTypeIntroNu sig cs ctx (SignatureSubstElim x y) b = assert_total $ idris_crash "unifyTypeIntroNu(SignatureSubstElim)"
  unifyTypeIntroNu sig cs ctx (TyEqTy p0 q0) (TyEqTy p1 q1) = M.do
    return (Success [  TypeConstraint ctx p0 p1,
                       TypeConstraint ctx q0 q1] [] [])
  unifyTypeIntroNu sig cs ctx (ElEqTy p0 q0 ty0) (ElEqTy p1 q1 ty1) = M.do
    return (Success [  TypeConstraint ctx ty0 ty1,
                       ElemConstraint ctx p0 p1 ty0,
                       ElemConstraint ctx q0 q1 ty0] [] [])
  unifyTypeIntroNu sig cs ctx _ _ = return (Stuck "unifyTypeIntroNu rule doesn't apply")

  public export
  unifyType : Signature -> Omega -> Context -> Typ -> Typ -> UnifyM Result
  unifyType sig cs ctx a b = M.do
    a <- liftM $ openEval sig cs a
    b <- liftM $ openEval sig cs b
    unifyTypeMetaNu sig cs ctx a b <||> unifyTypeElimNu sig cs ctx a b <||> unifyTypeIntroNu sig cs ctx a b

namespace SubstContextNF
  public export
  unify : Signature -> Omega -> SubstContextNF -> SubstContextNF -> Context -> Context -> UnifyM Result
  unify sig cs Terminal b source target = return (Success [] [] [])
  unify sig cs (WkN k) Terminal source target = return (Success [] [] [])
  unify sig cs (WkN k) (WkN j) source target =
    case (k == j) of
      True => return (Success [] [] [])
      False => return (Disunifier "↑ⁱ vs iᵏ where i ≠ k")
  unify sig cs (WkN k) (Ext sigma t) source (target :< (x, ty)) =
    return (Success [  SubstContextConstraint sigma (WkN (S k)) source target,
                       ElemConstraint source t (ContextVarElim k) (ContextSubstElim ty sigma)] [] [])
  unify sig cs (WkN k) (Ext sigma t) source target = return (Stuck "↑ⁿ vs (_, _) where the target context is not an extension")
  unify sig cs (Ext x y) Terminal source target = return (Success [] [] [])
  unify sig cs (Ext sigma t) (WkN k) source (target :< (x, ty)) =
    return (Success [  SubstContextConstraint sigma (WkN (S k)) source target,
                       ElemConstraint source t (ContextVarElim k) (ContextSubstElim ty sigma)] [] [])
  unify sig cs (Ext sigma t) (WkN k) source target = return (Stuck "↑ⁿ vs (_, _) where the target context is not an extension")
  unify sig cs (Ext sigma p) (Ext tau q) source (target :< (x, ty)) =
    return (Success [  SubstContextConstraint sigma tau source target,
                       ElemConstraint source p q (ContextSubstElim ty sigma)] [] [])
  unify sig cs (Ext sigma p) (Ext tau q) source target = return (Stuck "(_, _) vs (_, _) where the target context is not an extension")

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
  unify sig cs (TypeConstraint ctx a b) = M.do
    case !(liftM $ conv sig cs a b) of
      True => return (Success [] [] [])
      False => unifyType sig cs ctx a b
  unify sig cs (ElemConstraint ctx a b ty) = M.do
    case !(liftM $ conv sig cs a b) of
      True => return (Success [] [] [])
      False => unifyElem sig cs ctx a b ty
  unify sig cs (SubstContextConstraint sigma tau source target) = M.do
    case !(liftM $ conv sig cs sigma tau) of
      True => return (Success [] [] [])
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
addConstraint omega e = M.do
  x <- nextOmegaName
  return $ insert (x, toOmegaEntry e) omega

namespace Named
  ||| The name must be unique!
  public export
  newTypeMeta : Omega -> Context -> OmegaName -> MetaKind -> UnifyM Omega
  newTypeMeta omega ctx n k = M.do
    case lookup n omega of
      Just _ => criticalError "newTypeMeta, name already exists: \{n}"
      Nothing => return (insert (n, MetaType ctx k) omega)

  ||| The name must be unique!
  public export
  newElemMeta : Omega -> Context -> OmegaName -> Typ -> MetaKind -> UnifyM Omega
  newElemMeta omega ctx n ty k = M.do
    case lookup n omega of
      Just _ => criticalError "newElemMeta, name already exists: \{n}"
      Nothing => return (insert (n, MetaElem ctx ty k) omega)

namespace Nameless
  public export
  newTypeMeta : Omega -> Context -> MetaKind -> UnifyM (Omega, OmegaName)
  newTypeMeta omega ctx k = M.do
    n <- nextOmegaName
    return (!(Named.newTypeMeta omega ctx n k), n)

  public export
  newElemMeta : Omega -> Context -> Typ -> MetaKind -> UnifyM (Omega, OmegaName)
  newElemMeta omega ctx ty k = M.do
    n <- nextOmegaName
    {- case k of
      SolveByElaboration => print_ Debug STDOUT "Creating new elab-meta: \{n}"
      _ => return () -}
    return (!(Named.newElemMeta omega ctx n ty k), n)

public export
addConstraintN : Omega -> List ConstraintEntry -> UnifyM Omega
addConstraintN omega [] = return omega
addConstraintN omega (e :: es) = addConstraintN !(addConstraint omega e) es

public export
addMetaN : Omega -> List (Context, OmegaName, Either () Typ) -> UnifyM Omega
addMetaN sig [] = return sig
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
  prettyProgress : Signature -> Progress.Progress -> M (Doc Ann)
  prettyProgress sig (Success omega cs) = M.do
    return $
      "Success, sub-problems:"
       <+>
      hardline
       <+>
      !(prettyConstraints sig omega cs)
  prettyProgress sig (Stuck reason) = M.do
    return (pretty "Stuck, reason: \{reason}")
  prettyProgress sig (Disunifier reason) = M.do
    return (pretty "Disunifier, reason: \{reason}")

progressEntry : Signature -> Omega -> ConstraintEntry -> UnifyM Progress
progressEntry sig omega entry = M.do
  {- print_ Debug STDOUT "--------- Unifying ---------"
  print_ Debug STDOUT (renderDocTerm !(liftM $ prettyConstraintEntry sig omega entry)) -}
  let go : Signature -> Omega -> ConstraintEntry -> UnifyM Progress
      go sig cs e = M.do
        case !(unify sig cs e) of
          Success new metas is => M.do
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
            print_ Debug STDOUT (renderDocTerm !(liftM $ prettyOmega' sig omega (map metaToOmegaEntry metas)))
            print_ Debug STDOUT "Solutions:"
            print_ Debug STDOUT (renderDocTerm !(liftM $ prettyOmega' sig omega (map letToOmegaEntry is))) -}
            let cs = instantiateN cs is
            cs <- addMetaN cs metas
            return (Success cs (cast new))
          Stuck str => return (Stuck str)
          Disunifier str => return (Disunifier str)
  progress <- go sig omega entry
  {- print_ Debug STDOUT "Progress:"
  print_ Debug STDOUT (renderDocTerm !(liftM $ prettyProgress sig progress))
  print_ Debug STDOUT "-------------------------------" -}
  return progress

progressElemMetaNu : Signature -> Omega -> Context -> OmegaName -> Typ -> UnifyM MetaProgress
progressElemMetaNu sig omega ctx idx ZeroTy = return (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx OneTy = return (Success (insert (idx, LetElem ctx OneVal OneTy) omega) [] [])
progressElemMetaNu sig omega ctx idx UniverseTy = return (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx NatTy = return (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx ty@(PiTy x dom cod) = M.do
  f <- nextOmegaName
  return (Success (insert (idx, LetElem ctx (PiVal x dom cod (OmegaVarElim f Id)) ty) omega) [(ctx :< (x, dom), f, cod)] [])
progressElemMetaNu sig omega ctx idx ty@(ImplicitPiTy x dom cod) = M.do
  f <- nextOmegaName
  return (Success (insert (idx, LetElem ctx (ImplicitPiVal x dom cod (OmegaVarElim f Id)) ty) omega) [(ctx :< (x, dom), f, cod)] [])
progressElemMetaNu sig omega ctx idx ty@(SigmaTy x dom cod) = M.do
  a <- nextOmegaName
  b <- nextOmegaName
  return (Success
            (insert (idx, LetElem ctx (SigmaVal x dom cod (OmegaVarElim a Id) (OmegaVarElim b Id)) ty) omega)
            [ (ctx, a, dom), (ctx, b, (ContextSubstElim cod (Ext Id (OmegaVarElim a Id))))] []
         )
progressElemMetaNu sig omega ctx idx (TyEqTy a b) = return (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx (ElEqTy x y z) = return (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx (El x) = return (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx (ContextSubstElim x y) = assert_total $ idris_crash "progressElemMetaNu(ContextSubstElim)"
progressElemMetaNu sig omega ctx idx (SignatureSubstElim x y) = assert_total $ idris_crash "progressElemMetaNu(SignatureSubstElim)"
progressElemMetaNu sig omega ctx idx (OmegaVarElim str x) = return (Stuck "No canonical Elem exists")
progressElemMetaNu sig omega ctx idx (SignatureVarElim str x) = return (Stuck "No canonical Elem exists")

progressMeta : Signature -> Omega -> OmegaName -> MetaBindingEntry -> UnifyM MetaProgress
progressMeta sig omega idx (MetaType ctx _) = return (Stuck "Skipping Type meta")
progressMeta sig omega idx (MetaElem ctx ty NoSolve) = return (Stuck "Skipping NoSolve Elem meta")
progressMeta sig omega idx (MetaElem ctx ty SolveByElaboration) = return (Stuck "Skipping SolveByElaboration Elem meta")
progressMeta sig omega idx (MetaElem ctx ty SolveByUnification) = progressElemMetaNu sig omega ctx idx !(liftM $ openEval sig omega ty)

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
progressMetas sig omega [] True = return (Success omega)
progressMetas sig omega [] False = return Stuck
progressMetas sig omega ((idx, binding) :: rest) b = M.do
  case !(progressMeta sig omega idx binding) of
    Success omega newBindings newConstraints => M.do
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
progressEntries sig cs [] False = return (Stuck [])
progressEntries sig cs [] True = return (Success cs)
progressEntries sig cs (e :: es) progressMade =
  case !(progressEntry sig cs e) of
    Success cs' new => progressEntries sig cs' (new <>> es) True
    Stuck str =>
      case !(progressEntries sig !(addConstraint cs e) es progressMade) of
        Stuck list => return (Stuck ((e, str) :: list))
        Success omega => return (Success omega)
        Disunifier e s => return (Disunifier e s)
    Disunifier str => return (Disunifier e str)

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
     doFilter (idx, e) = do
       e <- mbMetaBindingEntry e
       pure (idx, e)

namespace BindingEntry
  ||| Extract meta bindings from Ω
  public export
  getMetaBindings : List (OmegaName, BindingEntry) -> List (OmegaName, MetaBindingEntry)
  getMetaBindings bindings = mapMaybe doFilter bindings
    where
     doFilter : (OmegaName, BindingEntry) -> Maybe (OmegaName, MetaBindingEntry)
     doFilter (idx, e) = do
       e <- mbMetaBindingEntry e
       pure (idx, e)

||| Extract bindings from Ω
getBindings : Omega -> List (OmegaName, BindingEntry)
getBindings omega = mapMaybe doFilter (List.inorder omega)
  where
   doFilter : (OmegaName, OmegaEntry) -> Maybe (OmegaName, BindingEntry)
   doFilter (idx, e) = do
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
progressEntriesFixpoint sig bindings constraints progress = M.do
  case !(progressEntries sig (toOmega bindings) constraints False) of
    Stuck list =>
      case progress of
        True => return (Success !(addConstraintN (toOmega bindings) constraints))
        False => M.do
          case !(progressMetas sig (toOmega bindings) (getMetaBindings bindings) False) of
            Success omega => progressEntriesFixpoint sig (getBindings omega) (getConstraints omega ++ constraints) True
            Stuck => return (Stuck list)
    Disunifier e str => return (Disunifier e str)
    Success omega => progressEntriesFixpoint sig (getBindings omega) (getConstraints omega) True

public export
solve : Signature -> Omega -> UnifyM Fixpoint
solve sig omega = progressEntriesFixpoint sig (getBindings omega) (getConstraints omega) False
