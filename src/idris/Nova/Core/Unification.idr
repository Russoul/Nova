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
import Nova.Core.Evaluation
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Pretty
import Nova.Core.Rigidity
import Nova.Core.Substitution

import Nova.Surface.SemanticToken

-- Unification is performed relative to a sub-relation of definitional equality:
-- (~) implies (=)

public export
record UnifySt where
  constructor MkUnifySt
  nextOmegaIdx : Nat

public export
initialUnifySt : UnifySt
initialUnifySt = MkUnifySt 0

public export
UnifyM : Type -> Type
  --                  vvvvvv for critical errors only
UnifyM = JustAMonad.M String UnifySt

public export
liftM : M a -> UnifyM a
liftM f = M.do
  st <- get
  mapState (const st) (const ()) f

public export
liftMMaybe : String -> M (Maybe a) -> UnifyM a
liftMMaybe err f = M.do
 case !(liftM f) of
   Just x => return x
   Nothing => throw err

public export
liftMEither : M (Either String a) -> UnifyM a
liftMEither f = M.do
 case !(liftM f) of
   Right x => return x
   Left err => throw err

public export
nextOmegaName : UnifyM OmegaName
nextOmegaName = M.do
  MkUnifySt idx <- get
  set (MkUnifySt (S idx))
  return ("?\{show idx}")

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
    invertNu sig omega ctx delta sigma (SigmaVal p q) = MMaybe.do
      p' <- invert sig omega ctx delta sigma p
      q' <- invert sig omega ctx delta sigma q
      return (SigmaVal p' q')
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
    invertNu sig omega ctx delta sigma (ZeroElim t) = MMaybe.do
      t' <- invert sig omega ctx delta sigma t
      return (ZeroElim t')
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
    invertNu sig omega ctx delta sigma TyEqVal = MMaybe.do return TyEqVal
    invertNu sig omega ctx delta sigma ElEqVal = MMaybe.do return ElEqVal

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
    occursNu sig omega (SigmaVal p q) k =
      occurs sig omega p k `or` occurs sig omega q k
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
    occursNu sig omega (ZeroElim t) k =
      occurs sig omega t k
    occursNu sig omega (NatElim x schema z y h s t) k =
      occurs sig omega schema k `or` occurs sig omega z k `or` occurs sig omega s k `or` occurs sig omega t k
    occursNu sig omega (ContextSubstElim x y) k = assert_total $ idris_crash "occursNu(ContextSubstElim)"
    occursNu sig omega (SignatureSubstElim x y) k = assert_total $ idris_crash "occursNu(SignatureSubstElim)"
    occursNu sig omega (ContextVarElim j) k = return False
    occursNu sig omega (SignatureVarElim j sigma) k = occurs sig omega sigma k
    occursNu sig omega (OmegaVarElim j sigma) k = return (j == k) `or` occurs sig omega sigma k
    occursNu sig omega (TyEqTy a b) k = occurs sig omega a k `or` occurs sig omega b k
    occursNu sig omega (ElEqTy a b ty) k = occurs sig omega a k `or` occurs sig omega b k `or` occurs sig omega ty k
    occursNu sig omega TyEqVal k = return False
    occursNu sig omega ElEqVal k = return False

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
  ||| Σ Ω Γ ⊦ a₀ ~ a₁ : A
  ||| A, a₀, a₁ are head-neutral w.r.t. substitution.
  public export
  unifyElemNu : Signature -> Omega -> Context -> Elem -> Elem -> Typ -> UnifyM Result
  unifyElemNu sig cs ctx a@(OmegaVarElim k0 sigma0) b@(OmegaVarElim k1 sigma1) ty = M.do
    let Just entry0 = lookup k0 cs
         | _ => assert_total $ idris_crash "unifyElemNu(OmegaVarElim(1))"
    let Just entry1 = lookup k1 cs
         | _ => assert_total $ idris_crash "unifyElemNu(OmegaVarElim(2))"
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
                 _ => assert_total $ idris_crash "unifyElemNu(SignatureVarElim, SignatureVarElim)(1)"
          False => return (Stuck "χᵢ vs χⱼ, where i ≠ j, flex")
  unifyElemNu sig cs ctx a@(OmegaVarElim k sigma) b ty = M.do
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
         MetaType {} => assert_total $ idris_crash "unifyElemNu(OmegaVarElim, _)(1)"
         LetElem {} => assert_total $ idris_crash "unifyElemNu(OmegaVarElim, _)(2)"
         LetType {} => assert_total $ idris_crash "unifyElemNu(OmegaVarElim, _)(3)"
         TypeConstraint {} => assert_total $ idris_crash "unifyElemNu(OmegaVarElim, _)(4)"
         ElemConstraint {} => assert_total $ idris_crash "unifyElemNu(OmegaVarElim, _)(5)"
         SubstContextConstraint {} => assert_total $ idris_crash "unifyElemNu(OmegaVarElim, _)(6)"
  unifyElemNu sig cs ctx a b@(OmegaVarElim k sigma) ty = M.do
    -- we now that a is rigid here
    case !(liftM $ isRigid sig cs b) of
      True => return (Disunifier "rigid χᵢ vs something else rigid")
      False => M.do
       let Just entry = lookup k cs
            | _ => assert_total $ idris_crash "unifyElemNu(SignatureVarElim(3))"
       case entry of
         -- We've got a hole, try solving it
         MetaElem hctx hty SolveByUnification => liftM $ trySolveElem sig cs ctx k hctx hty sigma a ty
         MetaElem hctx hty SolveByElaboration => return (Stuck "?(solve by elaboration) vs something else rigid")
         MetaElem hctx hty NoSolve => return (Stuck "?(no solve) vs something else rigid")
         MetaType {} => assert_total $ idris_crash "unifyElemNu(OmegaVarElim, _)(1)"
         LetElem {} => assert_total $ idris_crash "unifyElemNu(OmegaVarElim, _)(2)"
         LetType {} => assert_total $ idris_crash "unifyElemNu(OmegaVarElim, _)(3)"
         TypeConstraint {} => assert_total $ idris_crash "unifyElemNu(OmegaVarElim, _)(4)"
         ElemConstraint {} => assert_total $ idris_crash "unifyElemNu(OmegaVarElim, _)(5)"
         SubstContextConstraint {} => assert_total $ idris_crash "unifyElemNu(OmegaVarElim, _)(6)"
  unifyElemNu sig cs ctx (PiTy x0 dom0 cod0) (PiTy x1 dom1 cod1) ty = FailSt.do
    return (Success [ ElemConstraint ctx dom0 dom1 UniverseTy
                    , ElemConstraint (ctx :< (x0, El dom0)) cod0 cod1 UniverseTy
                    ]
                    []
                    []
           )
  unifyElemNu sig cs ctx (PiTy x0 dom0 cod0) b ty = M.do
    return (Disunifier "Π vs something else rigid")
  unifyElemNu sig cs ctx (ImplicitPiTy x0 dom0 cod0) (ImplicitPiTy x1 dom1 cod1) ty = FailSt.do
    return (Success [ ElemConstraint ctx dom0 dom1 UniverseTy
                    , ElemConstraint (ctx :< (x0, El dom0)) cod0 cod1 UniverseTy
                    ]
                    []
                    []
           )
  unifyElemNu sig cs ctx (ImplicitPiTy x0 dom0 cod0) b ty = M.do
    return (Disunifier "Πⁱ vs something else rigid")
  unifyElemNu sig cs ctx (SigmaTy x0 dom0 cod0) (SigmaTy x1 dom1 cod1) ty = FailSt.do
    return (Success [ ElemConstraint ctx dom0 dom1 UniverseTy
                    , ElemConstraint (ctx :< (x0, El dom0)) cod0 cod1 UniverseTy
                    ]
                    []
                    []
           )
  unifyElemNu sig cs ctx (SigmaTy x0 dom0 cod0) b ty = M.do
    return (Disunifier "Σ vs something else rigid")
  unifyElemNu sig cs ctx (PiVal x0 dom0 cod0 f0) (PiVal x1 dom1 cod1 f1) ty = FailSt.do
    return (Success [ElemConstraint (ctx :< (x0, dom0)) f0 f1 cod0]
                    []
                    []
           )
  unifyElemNu sig cs ctx (PiVal {}) b ty = M.do
    return (Disunifier "λ vs something else rigid")
  unifyElemNu sig cs ctx (ImplicitPiVal x0 dom0 cod0 f0) (ImplicitPiVal x1 dom1 cod1 f1) ty = FailSt.do
    return (Success [ElemConstraint (ctx :< (x0, dom0)) f0 f1 cod0]
                    []
                    []
           )
  unifyElemNu sig cs ctx (ImplicitPiVal {}) b ty = M.do
    return (Disunifier "λⁱ vs something else rigid")
  unifyElemNu sig cs ctx (SigmaVal p0 q0) (SigmaVal p1 q1) (SigmaTy x a b) = FailSt.do
    return (Success [ElemConstraint ctx p0 p1 a, ElemConstraint ctx q0 q1 (ContextSubstElim b (Ext Id p0))]
                    []
                    []
           )
  unifyElemNu sig cs ctx (SigmaVal p0 q0) (SigmaVal p1 q1) _ = FailSt.do
    return (Stuck "Type is not a Σ")
  unifyElemNu sig cs ctx (SigmaVal p q) b ty = M.do
    return (Disunifier "(_, _) vs something else rigid")
  unifyElemNu sig cs ctx (PiElim f0 x0 dom0 cod0 e0) (PiElim f1 x1 dom1 cod1 e1) ty = M.do
    return (Success [TypeConstraint ctx dom0 dom1
                    , TypeConstraint (ctx :< (x0, dom0)) cod0 cod1
                    , ElemConstraint ctx f0 f1 (PiTy x0 dom0 cod0)
                    , ElemConstraint ctx e0 e1 dom0
                    ]
                    []
                    []
           )
  unifyElemNu sig cs ctx (PiElim f0 x0 dom0 cod0 e0) b ty = M.do
    return (Disunifier "app vs something else rigid")
  unifyElemNu sig cs ctx (ImplicitPiElim f0 x0 dom0 cod0 e0) (ImplicitPiElim f1 x1 dom1 cod1 e1) ty = M.do
    return (Success [TypeConstraint ctx dom0 dom1
                    , TypeConstraint (ctx :< (x0, dom0)) cod0 cod1
                    , ElemConstraint ctx f0 f1 (ImplicitPiTy x0 dom0 cod0)
                    , ElemConstraint ctx e0 e1 dom0
                    ]
                    []
                    []
           )
  unifyElemNu sig cs ctx (ImplicitPiElim f0 x0 dom0 cod0 e0) b ty = M.do
    return (Disunifier "appⁱ vs something else rigid")
  unifyElemNu sig cs ctx (SigmaElim1 f0 x0 dom0 cod0) (SigmaElim1 f1 x1 dom1 cod1) ty = M.do
    return (Success [ TypeConstraint ctx dom0 dom1
                    , TypeConstraint (ctx :< (x0, dom0)) cod0 cod1
                    , ElemConstraint ctx f0 f1 (SigmaTy x0 dom0 cod0)
                    ]
                    []
                    []
           )
  unifyElemNu sig cs ctx (SigmaElim1 f0 x0 dom0 cod0) b ty = M.do
    return (Disunifier "π₁ vs something else rigid")
  unifyElemNu sig cs ctx (SigmaElim2 f0 x0 dom0 cod0) (SigmaElim2 f1 x1 dom1 cod1) ty = M.do
    return (Success [TypeConstraint ctx dom0 dom1
                    , TypeConstraint (ctx :< (x0, dom0)) cod0 cod1
                    , ElemConstraint ctx f0 f1 (SigmaTy x0 dom0 cod0)
                    ]
                    []
                    []
           )
  unifyElemNu sig cs ctx (SigmaElim2 f0 x0 dom0 cod0) b ty = M.do
    return (Disunifier "π₂ vs something else rigid")
  unifyElemNu sig cs ctx NatVal0 NatVal0 ty =
    return (Success [] [] [])
  unifyElemNu sig cs ctx NatVal0 b ty = M.do
    return (Disunifier "Z vs something else rigid")
  unifyElemNu sig cs ctx OneVal OneVal _ =
    return (Success [] [] [])
  unifyElemNu sig cs ctx OneVal b ty = M.do
    return (Disunifier "() vs something else rigid")
  unifyElemNu sig cs ctx (NatVal1 t0) (NatVal1 t1) ty = M.do
    return (Success [ ElemConstraint ctx t0 t1 NatTy] [] [])
  unifyElemNu sig cs ctx (NatVal1 x) b ty = M.do
    return (Disunifier "S _ vs something else rigid")
  unifyElemNu sig cs ctx NatTy NatTy ty = return (Success [] [] [])
  unifyElemNu sig cs ctx NatTy b ty = M.do
    return (Disunifier "ℕ vs something else rigid")
  unifyElemNu sig cs ctx ZeroTy ZeroTy ty = return (Success [] [] [])
  unifyElemNu sig cs ctx ZeroTy b ty = M.do
    return (Disunifier "𝟘 vs something else rigid")
  unifyElemNu sig cs ctx OneTy OneTy ty = return (Success [] [] [])
  unifyElemNu sig cs ctx OneTy b ty = M.do
    return (Disunifier "𝟙 vs something else rigid")
  unifyElemNu sig cs ctx (NatElim x0 schema0 z0 y0 h0 s0 t0) (NatElim x1 schema1 z1 y1 h1 s1 t1) ty = M.do
    return (Success [  TypeConstraint (ctx :< (x0, NatTy)) schema0 schema1,
                       ElemConstraint ctx z0 z1 (ContextSubstElim schema0 (Ext Id NatVal0)),
                       ElemConstraint (ctx :< (y0, NatTy) :< (h0, schema0)) s0 s1 (ContextSubstElim schema0 (Ext (WkN 2) (NatVal1 (CtxVarN 1)))),
                       ElemConstraint ctx t0 t1 NatTy] [] [])

  unifyElemNu sig cs ctx (NatElim x0 schema0 z0 y0 h0 s0 t0) b ty = M.do
    return (Disunifier "ℕ-elim vs something else rigid")
  unifyElemNu sig cs ctx (ZeroElim t0) (ZeroElim t1) ty = M.do
    return (Success [ElemConstraint ctx t0 t1 ZeroTy] [] [])
  unifyElemNu sig cs ctx (ZeroElim t0) b ty = M.do
    return (Disunifier "𝟘-elim vs something else rigid")
  unifyElemNu sig cs ctx (ContextSubstElim x y) b ty = assert_total $ idris_crash "unifyElemNu(ContextSubstElim)"
  unifyElemNu sig cs ctx (SignatureSubstElim x y) b ty = assert_total $ idris_crash "unifyElemNu(SignatureSubstElim)"
  unifyElemNu sig cs ctx (ContextVarElim k0) (ContextVarElim k1) ty = M.do
    case k0 == k1 of
      True => return (Success [] [] [])
      False => return (Disunifier "xᵢ vs xⱼ where i ≠ j")
  unifyElemNu sig cs ctx (ContextVarElim k) b ty = M.do
    return (Disunifier "xᵢ vs something else rigid")
  unifyElemNu sig cs ctx (TyEqTy p0 q0) (TyEqTy p1 q1) _ = M.do
    return (Success [  ElemConstraint ctx p0 p1 UniverseTy,
                       ElemConstraint ctx q0 q1 UniverseTy] [] [])
  unifyElemNu sig cs ctx (TyEqTy p0 q0) b _ = M.do
    return (Disunifier "(≡) vs something else rigid")
  unifyElemNu sig cs ctx (ElEqTy p0 q0 ty0) (ElEqTy p1 q1 ty1) _ = M.do
    return (Success [  ElemConstraint ctx ty0 ty1 UniverseTy,
                       ElemConstraint ctx p0 p1 (El ty0),
                       ElemConstraint ctx q0 q1 (El ty0)] [] [])
  unifyElemNu sig cs ctx (ElEqTy p0 q0 ty0) b _ = M.do
    return (Disunifier "(≡) vs something else rigid")
  unifyElemNu sig cs ctx TyEqVal TyEqVal ty = return (Success [] [] [])
  unifyElemNu sig cs ctx TyEqVal b ty = M.do
    return (Disunifier "Refl vs something else rigid")
  unifyElemNu sig cs ctx ElEqVal ElEqVal ty = return (Success [] [] [])
  unifyElemNu sig cs ctx ElEqVal b ty = M.do
    return (Disunifier "Refl vs something else rigid")
  unifyElemNu sig cs ctx (SignatureVarElim k0 sigma0) (SignatureVarElim k1 sigma1) ty = M.do
    case (k0 == k1) of
      False => return (Disunifier "χᵢ vs χⱼ where i ≠ j")
      True =>
        return (Success [ SubstContextConstraint sigma0 sigma1 ctx (getCtx k0)] [] [])
       where
        getCtx : Nat -> Context
        getCtx k =
          case (splitAt sig k) of
            Nothing => assert_total $ idris_crash "invertNu(SignatureVarElim)(1)"
            Just (_, (_, e), rest) =>
              case subst e (WkN $ 1 + length rest) of
               ElemEntry xi {} => xi
               LetElemEntry xi {} => xi
  unifyElemNu sig cs ctx (SignatureVarElim k0 sigma0) b ty = M.do
    return (Disunifier "χᵢ vs something else rigid")

  public export
  unifyElem : Signature -> Omega -> Context -> Elem -> Elem -> Typ -> UnifyM Result
  unifyElem sig cs ctx a b ty = M.do
    unifyElemNu sig cs ctx !(liftM $ openEval sig cs a) !(liftM $ openEval sig cs b) !(liftM $ openEval sig cs ty)

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
  unifyElAgainstRigid sig omega ctx el NatTy = M.do
    return (Success [ ElemConstraint ctx el NatTy UniverseTy] [] [])
  unifyElAgainstRigid sig omega ctx el (PiTy x dom cod) = M.do
    dom' <- nextOmegaName
    cod' <- nextOmegaName
    return (Success [ElemConstraint ctx el (PiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id)) UniverseTy]
                    [(ctx, dom', Right UniverseTy), (ctx :< (x, El $ OmegaVarElim dom' Id), cod', Right UniverseTy)]
                    []
           )
  unifyElAgainstRigid sig omega ctx el (ImplicitPiTy x dom cod) = M.do
    dom' <- nextOmegaName
    cod' <- nextOmegaName
    return (Success [ElemConstraint ctx el (ImplicitPiTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id)) UniverseTy]
                    [(ctx, dom', Right UniverseTy), (ctx :< (x, El $ OmegaVarElim dom' Id), cod', Right UniverseTy)]
                    []
           )
  unifyElAgainstRigid sig omega ctx el (SigmaTy x dom cod) = M.do
    dom' <- nextOmegaName
    cod' <- nextOmegaName
    return (Success [ElemConstraint ctx el (SigmaTy x (OmegaVarElim dom' Id) (OmegaVarElim cod' Id)) UniverseTy]
                    [(ctx, dom', Right UniverseTy), (ctx :< (x, El $ OmegaVarElim dom' Id), cod', Right UniverseTy)]
                    []
           )
  unifyElAgainstRigid sig omega ctx el (TyEqTy a0 a1) = M.do
    a0' <- nextOmegaName
    a1' <- nextOmegaName
    return (Success [ElemConstraint ctx el (TyEqTy (OmegaVarElim a0' Id) (OmegaVarElim a1' Id)) UniverseTy]
                    [(ctx, a0', Right UniverseTy), (ctx, a1', Right UniverseTy)]
                    []
           )
  unifyElAgainstRigid sig omega ctx el (ElEqTy a0 a1 ty) = M.do
    a0' <- nextOmegaName
    a1' <- nextOmegaName
    ty' <- nextOmegaName
    return (Success [ElemConstraint ctx el (ElEqTy (OmegaVarElim a0' Id) (OmegaVarElim a1' Id) (OmegaVarElim ty' Id)) UniverseTy]
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
  unifyTypeNu : Signature -> Omega -> Context -> Typ -> Typ -> UnifyM Result
  unifyTypeNu sig cs ctx a@(OmegaVarElim k0 sigma0) b@(OmegaVarElim k1 sigma1) = M.do
    let Just entry0 = lookup k0 cs
         | _ => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim(1))"
    let Just entry1 = lookup k1 cs
         | _ => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim(2))"
    case (entry0, entry1) of
      -- Both sides are holes, try solving for each side.
      (MetaType hctx0 SolveByUnification, MetaType hctx1 SolveByUnification) =>
         case !(liftM $ trySolveType sig cs ctx k0 hctx0 sigma0 b) of
           Success cs [] sols => return (Success cs [] sols)
           Success cs (_ :: _) sols => assert_total $ idris_crash "unifyTypeNu(Meta, Meta)"
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
                  _ => assert_total $ idris_crash "unifyTypeNu(SignatureVarElim, SignatureVarElim)(1)"
          False => return (Stuck "χᵢ vs χⱼ, where i ≠ j, flex")
  unifyTypeNu sig cs ctx a@(OmegaVarElim k sigma) b = M.do
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
         MetaElem hctx _ _ => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim, _)(7)"
         LetElem {} => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim, _)(2)"
         LetType {} => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim, _)(3)"
         TypeConstraint {} => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim, _)(4)"
         ElemConstraint {} => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim, _)(5)"
         SubstContextConstraint {} => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim, _)(6)"
  unifyTypeNu sig cs ctx a b@(OmegaVarElim k sigma) = M.do
    case (!(liftM $ isRigid sig cs a), !(liftM $ isRigid sig cs b))  of
      (True, True) => return (Disunifier "rigid χᵢ vs something else rigid")
      (False, True) => return (Stuck "rigid χᵢ vs something else flex")
      (_, False) => M.do
       let Just entry = lookup k cs
            | _ => assert_total $ idris_crash "unifyTypeNu(SignatureVarElim(3))"
       case entry of
         -- We've got a hole, try solving it
         MetaType hctx SolveByUnification => liftM $ trySolveType sig cs ctx k hctx sigma a
         MetaType hctx SolveByElaboration => return (Stuck "?(solve by elaboration) vs something else rigid")
         MetaType hctx NoSolve => return (Stuck "?(no solve) vs something else rigid")
         -- This is possible, when the type is 𝕌
         MetaElem hctx _ _ => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim, _)(7)"
         LetElem {} => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim, _)(2)"
         LetType {} => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim, _)(3)"
         TypeConstraint {} => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim, _)(4)"
         ElemConstraint {} => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim, _)(5)"
         SubstContextConstraint {} => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim, _)(6)"
  unifyTypeNu sig cs ctx (El a0) (El a1) = M.do
    case !(liftM $ isRigid sig cs a0) || !(liftM $ isRigid sig cs a1) of
      True => return (Success [ElemConstraint ctx a0 a1 UniverseTy] [] [])
      False => return (Stuck "El a₀ vs El a₁ where a₀ doesn't convert with a₁, both are flex")
  unifyTypeNu sig cs ctx (El el) other = M.do
    case !(liftM $ isRigid sig cs other) of
      True => unifyElAgainstRigid sig cs ctx el other
      False => return (Stuck "El _ vs something else flex")
  unifyTypeNu sig cs ctx other (El el) = M.do
    case !(liftM $ isRigid sig cs other) of
      True => unifyElAgainstRigid sig cs ctx el other
      False => return (Stuck "El _ vs something else flex")
  unifyTypeNu sig cs ctx (PiTy x0 dom0 cod0) (PiTy x1 dom1 cod1) = FailSt.do
    return (Success [ TypeConstraint ctx dom0 dom1
                    , TypeConstraint (ctx :< (x0, dom0)) cod0 cod1
                    ]
                    []
                    []
           )
  unifyTypeNu sig cs ctx (PiTy {}) other = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "Π vs something else rigid")
      False => return (Stuck "Π vs something else flex")
  unifyTypeNu sig cs ctx other (PiTy {}) = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "Π vs something else rigid")
      False => return (Stuck "Π vs something else flex")
  unifyTypeNu sig cs ctx (ImplicitPiTy x0 dom0 cod0) (ImplicitPiTy x1 dom1 cod1) = FailSt.do
    return (Success [ TypeConstraint ctx dom0 dom1
                    , TypeConstraint (ctx :< (x0, dom0)) cod0 cod1
                    ]
                    []
                    []
           )
  unifyTypeNu sig cs ctx (ImplicitPiTy {}) other = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "Πⁱ vs something else rigid")
      False => return (Stuck "Πⁱ vs something else flex")
  unifyTypeNu sig cs ctx other (ImplicitPiTy {}) = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "Πⁱ vs something else rigid")
      False => return (Stuck "Πⁱ vs something else flex")
  unifyTypeNu sig cs ctx (SigmaTy x0 dom0 cod0) (SigmaTy x1 dom1 cod1) = FailSt.do
    return (Success [ TypeConstraint ctx dom0 dom1
                    , TypeConstraint (ctx :< (x0, dom0)) cod0 cod1
                    ]
                    []
                    []
           )
  unifyTypeNu sig cs ctx (SigmaTy {}) other = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "Σ vs something else rigid")
      False => return (Stuck "Σ vs something else flex")
  unifyTypeNu sig cs ctx other (SigmaTy {}) = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "Σ vs something else rigid")
      False => return (Stuck "Σ vs something else flex")
  unifyTypeNu sig cs ctx UniverseTy UniverseTy =
    return (Success [] [] [])
  unifyTypeNu sig cs ctx UniverseTy other = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "𝕌 vs something else rigid")
      False => return (Stuck "𝕌 vs something else flex")
  unifyTypeNu sig cs ctx other UniverseTy = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "𝕌 vs something else rigid")
      False => return (Stuck "𝕌 vs something else flex")
  unifyTypeNu sig cs ctx NatTy NatTy = return (Success [] [] [])
  unifyTypeNu sig cs ctx NatTy other = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "ℕ vs something else rigid")
      False => return (Stuck "ℕ vs something else flex")
  unifyTypeNu sig cs ctx other NatTy = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "ℕ vs something else rigid")
      False => return (Stuck "ℕ vs something else flex")
  unifyTypeNu sig cs ctx ZeroTy ZeroTy = return (Success [] [] [])
  unifyTypeNu sig cs ctx ZeroTy other = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "𝟘 vs something else rigid")
      False => return (Stuck "𝟘 vs something else flex")
  unifyTypeNu sig cs ctx other ZeroTy = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "𝟘 vs something else rigid")
      False => return (Stuck "𝟘 vs something else flex")
  unifyTypeNu sig cs ctx OneTy OneTy = return (Success [] [] [])
  unifyTypeNu sig cs ctx OneTy other = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "𝟙 vs something else rigid")
      False => return (Stuck "𝟙 vs something else flex")
  unifyTypeNu sig cs ctx other OneTy = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "𝟙 vs something else rigid")
      False => return (Stuck "𝟙 vs something else flex")
  unifyTypeNu sig cs ctx (ContextSubstElim x y) b = assert_total $ idris_crash "unifyTypeNu(ContextSubstElim)"
  unifyTypeNu sig cs ctx (SignatureSubstElim x y) b = assert_total $ idris_crash "unifyTypeNu(SignatureSubstElim)"
  unifyTypeNu sig cs ctx (TyEqTy p0 q0) (TyEqTy p1 q1) = M.do
    return (Success [  TypeConstraint ctx p0 p1,
                       TypeConstraint ctx q0 q1] [] [])
  unifyTypeNu sig cs ctx (TyEqTy {}) other = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "(≡) vs something else rigid")
      False => return (Stuck "(≡) vs something else flex")
  unifyTypeNu sig cs ctx other (TyEqTy {}) = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "(≡) vs something else rigid")
      False => return (Stuck "(≡) vs something else flex")
  unifyTypeNu sig cs ctx (ElEqTy p0 q0 ty0) (ElEqTy p1 q1 ty1) = M.do
    return (Success [  TypeConstraint ctx ty0 ty1,
                       ElemConstraint ctx p0 p1 ty0,
                       ElemConstraint ctx q0 q1 ty0] [] [])
  unifyTypeNu sig cs ctx (ElEqTy {}) other = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "(≡) vs something else rigid")
      False => return (Stuck "(≡) vs something else flex")
  unifyTypeNu sig cs ctx other (ElEqTy {}) = M.do
    case !(liftM $ isRigid sig cs other) of
      True => return (Disunifier "(≡) vs something else rigid")
      False => return (Stuck "(≡) vs something else flex")
  unifyTypeNu sig cs ctx _ _ = assert_total $ idris_crash "unifyTypeNu"

  public export
  unifyType : Signature -> Omega -> Context -> Typ -> Typ -> UnifyM Result
  unifyType sig cs ctx a b = M.do
    unifyTypeNu sig cs ctx !(liftM $ openEval sig cs a) !(liftM $ openEval sig cs b)

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
      Just _ => throw "newTypeMeta, name already exists: \{n}"
      Nothing => return (insert (n, MetaType ctx k) omega)

  ||| The name must be unique!
  public export
  newElemMeta : Omega -> Context -> OmegaName -> Typ -> MetaKind -> UnifyM Omega
  newElemMeta omega ctx n ty k = M.do
    case lookup n omega of
      Just _ => throw "newElemMeta, name already exists: \{n}"
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

progressEntry : Signature -> Omega -> ConstraintEntry -> UnifyM Progress
progressEntry sig cs e = M.do
  case !(unify sig cs e) of
    Success new metas is => M.do
      let cs = instantiateN cs is
      cs <- addMetaN cs metas
      return (Success cs (cast new))
    Stuck str => return (Stuck str)
    Disunifier str => return (Disunifier str)

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

||| Remove all constraints from Ω.
onlyMetas : Omega -> Omega
onlyMetas omega = fromList $ mapMaybe H (List.inorder omega)
 where
  H : (OmegaName, OmegaEntry) -> Maybe (OmegaName, OmegaEntry)
  H (x, LetElem ctx rhs ty) = Just (x, LetElem ctx rhs ty)
  H (x, MetaElem ctx ty s) = Just (x, MetaElem ctx ty s)
  H (x, LetType ctx rhs) = Just (x, LetType ctx rhs)
  H (x, MetaType ctx s) = Just (x, MetaType ctx s)
  H _ = Nothing

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
progressEntriesFixpoint : Signature -> Omega -> List ConstraintEntry -> Bool -> UnifyM Fixpoint
progressEntriesFixpoint sig cs todo progress = M.do
  case !(progressEntries sig cs todo False) of
    Stuck list =>
      case progress of
        True => return (Success !(addConstraintN cs todo))
        False => return (Stuck list)
    Disunifier e str => return (Disunifier e str)
    Success cs' => progressEntriesFixpoint sig (onlyMetas cs') (getConstraints cs') True

public export
solve : Signature -> Omega -> UnifyM Fixpoint
solve sig cs = progressEntriesFixpoint sig (onlyMetas cs) (getConstraints cs) False
