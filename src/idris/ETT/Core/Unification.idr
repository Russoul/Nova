module ETT.Core.Unification

import Data.List
import Data.SnocList
import Data.Util
import Data.Maybe
import Data.AVL

import ETT.Core.Language
import ETT.Core.Monad
import ETT.Core.Substitution
import ETT.Core.Evaluation
import ETT.Core.Shrinking


-- Unification is performed relative to a sub-relation of definitional equality:
-- (~) implies (=)

public export
record UnifySt where
  constructor MkUnifySt
  nextOmegaIdx : Nat

public export
UnifyM : Type -> Type
UnifyM = JustAMonad.M String UnifySt

public export
liftM : M a -> UnifyM a
liftM f = M.do
  st <- get
  mapState (const st) (const ()) f

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
    Success : List ConstraintEntry -> (sols : List (OmegaName, Elem)) -> Result
    ||| A step has *not* been made.
    Stuck : String -> Result
    ||| Constraint is contradictive.
    Disunifier : String -> Result

||| A term head-neutral w.r.t. open-evaluation is rigid if
||| there is no (~) that changes its constructor.
public export
isRigid : Signature -> Omega -> Elem -> M Bool
isRigid sig omega (PiTy str x y) = return True
isRigid sig omega (PiVal str x y z) = return True
isRigid sig omega (PiElim x str y z w) = return True
isRigid sig omega Universe = return True
isRigid sig omega NatVal0 = return True
isRigid sig omega (NatVal1 x) = return True
isRigid sig omega NatTy = return True
isRigid sig omega (NatElim str x y str1 str2 z w) = return True
isRigid sig omega (ContextSubstElim x y) = assert_total $ idris_crash "isRigid(ContextSubstElim)"
isRigid sig omega (SignatureSubstElim x y) = assert_total $ idris_crash "isRigid(SignatureSubstElim)"
isRigid sig omega (ContextVarElim k) = return True
isRigid sig omega (SignatureVarElim k sigma) = return True
isRigid sig omega (OmegaVarElim x sigma) =
  case (lookup x omega) of
    Just (LetElem {}) => assert_total $ idris_crash "isRigid(SignatureVarElim)(1)"
    Just (LetType {}) => assert_total $ idris_crash "isRigid(SignatureVarElim)(1')"
    Just (MetaElem _ _ SolveByUnification) => return False
    Just (MetaElem _ _ SolveByElaboration) => return True
    Just (MetaType _ SolveByUnification) => return False
    Just (MetaType _ SolveByElaboration) => return True
    Just _ => assert_total $ idris_crash "isRigid(SignatureVarElim)(2)"
    Nothing => assert_total $ idris_crash "isRigid(SignatureVarElim)(3)"
isRigid sig omega (EqTy x y z) = return True
isRigid sig omega EqVal = return True

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
          -> Mb SubstContext
    invert sig omega sigma Terminal gamma delta xi = Mb.do return Terminal
    -- σ : Γ₀ Γ₁ ⇒ Δ
    -- ↑(Γ₁) : Γ₀ Γ₁ ⇒ Γ₀
    -- ? : Δ ⇒ Γ₀ such that ? ∘ σ ~ ↑(Γ₁)
    --
    -- in that case ↑ᵏ = ·
    invert sig omega sigma (WkN k) gamma delta Empty = Mb.do return Terminal
    -- in that case ↑ᵏ = (↑ᵏ⁺¹, k)
    invert sig omega sigma (WkN k) gamma delta xi@(Ext _ _ _) =
      SubstContextNF.invert sig omega sigma (Ext (WkN (S k)) (ContextVarElim k)) gamma delta xi
    -- TODO: IDK how to find the inverse in that case:
    invert sig omega sigma (WkN k) gamma delta (SignatureVarElim j) = nothing
    invert sig omega sigma (Ext tau t) gamma delta (Ext xi {}) = Mb.do
      tau' <- invert sig omega sigma tau gamma delta xi
      t' <- invert sig omega gamma delta sigma t
      return (Ext tau' t')
    invert sig omega sigma (Ext tau t) gamma delta _ = Mb.do
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
          -> Mb SubstContext
    invert sig omega sigma tau = invert sig omega sigma (eval tau)

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
            -> Mb Elem
    invertNu sig omega ctx delta sigma (PiTy x dom cod) = Mb.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (Ext ctx x dom) (Ext delta x dom') (Under sigma) cod
      return (PiTy x dom' cod')
    invertNu sig omega ctx delta sigma (PiVal x dom cod f) = Mb.do
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (Ext ctx x dom) (Ext delta x dom') (Under sigma) cod
      f' <- invert sig omega (Ext ctx x dom) (Ext delta x dom') (Under sigma) f
      return (PiVal x dom' cod' f')
    invertNu sig omega ctx delta sigma (PiElim f x dom cod e) = Mb.do
      f' <- invert sig omega ctx delta sigma f
      dom' <- invert sig omega ctx delta sigma dom
      cod' <- invert sig omega (Ext ctx x dom) (Ext delta x dom') (Under sigma) cod
      e' <- invert sig omega ctx delta sigma e
      return (PiElim f' x dom' cod' e')
    invertNu sig omega ctx delta sigma Universe = Mb.do return Universe
    invertNu sig omega ctx delta sigma NatVal0 = Mb.do return NatVal0
    invertNu sig omega ctx delta sigma (NatVal1 t) = Mb.do
      t <- invert sig omega ctx delta sigma t
      return (NatVal1 t)
    invertNu sig omega ctx delta sigma NatTy = Mb.do return NatTy
    invertNu sig omega ctx delta sigma (NatElim x schema z y h s t) = Mb.do
      schema' <- invert sig omega (Ext ctx x NatTy) (Ext delta x NatTy) (Under sigma) schema
      z' <- invert sig omega ctx delta sigma z
      s' <- invert sig omega (Ext (Ext ctx y NatTy) h schema) (Ext (Ext delta y NatTy) h schema') (Under (Under sigma)) s
      t' <- invert sig omega ctx delta sigma t
      return (NatElim x schema' z' y h s' t')
    invertNu sig omega ctx delta sigma (ContextSubstElim x y) = assert_total $ idris_crash "invertNu(ContextSubstElim)"
    invertNu sig omega ctx delta sigma (SignatureSubstElim x y) = assert_total $ idris_crash "invertNu(SignatureSubstElim)"
    invertNu sig omega ctx delta sigma (ContextVarElim k) = Mb.do
      index <- go sigma 0
      return (ContextVarElim index)
     where
      mutual
        goNu : SubstContextNF -> Nat -> Mb Nat
        goNu Terminal index = nothing
        -- ↑ⁱ
        goNu (WkN i) index =
          case i < k of
            -- We won't find k
            True => nothing
            -- We'll find k
            False => return (index + (i `minus` k))
        -- due to the conditions imposed on σ, t must be a variable up to (~)
        goNu (Ext sigma t) index = Mb.do
          case !(liftM $ openEval sig omega t) of
            ContextVarElim i =>
              case (i == k) of
                True => return index
                False => go sigma (S index)
            _ => assert_total $ idris_crash "invertNu(ContextVarElim)"

        go : SubstContext -> Nat -> Mb Nat
        go sigma index = goNu (eval sigma) index
    -- σ : Γ ⇒ Δ
    -- Γ ⊦ χᵢ (τ : Γ ⇒ Ω)
    -- Δ ⊦ χᵢ (ρ : Δ ⇒ Ω)
    -- Γ ⊦ χᵢ (ρ ∘ σ) = χᵢ τ
    -- that is, we need to find ρ : Δ ⇒ Ω
    -- such that (ρ ∘ σ) ~ τ
    invertNu sig omega ctx delta sigma (SignatureVarElim k tau) = Mb.do
      tau' <- invert sig omega sigma tau ctx delta getCtx
      return (SignatureVarElim k tau')
     where
      getCtx : Context
      getCtx =
        case (splitAt sig k) of
          Nothing => assert_total $ idris_crash "invertNu(SignatureVarElim)(1)"
          Just (_, (_, e), rest) =>
            case subst e (WkN $ 1 + length rest) of
             CtxEntry => assert_total $ idris_crash "invertNu(SignatureVarElim)(2)"
             TypeEntry xi => xi
             ElemEntry xi {} => xi
             LetElemEntry xi {} => xi
             EqTyEntry {} => assert_total $ idris_crash "invertNu(SignatureVarElim)(3)"
    invertNu sig omega ctx delta sigma (OmegaVarElim k tau) = Mb.do
      tau' <- invert sig omega sigma tau ctx delta getOmega
      return (OmegaVarElim k tau')
     where
      getOmega : Context
      getOmega =
        case (lookup k omega) of
          Nothing => assert_total $ idris_crash "invertNu(OmegaVarElim)(1)"
          Just (LetElem xi {}) => xi
          Just (MetaElem xi {}) => xi
          Just (LetType xi {}) => xi
          Just (MetaType xi {}) => xi
          Just _ => assert_total $ idris_crash "invertNu(OmegaVarElim)(2)"
    invertNu sig omega ctx delta sigma (EqTy a b ty) = Mb.do
      a <- invert sig omega ctx delta sigma a
      b <- invert sig omega ctx delta sigma b
      ty <- invert sig omega ctx delta sigma ty
      return (EqTy a b ty)
    invertNu sig omega ctx delta sigma EqVal = Mb.do return EqVal

    public export
    invert : Signature -> Omega -> Context -> Context -> SubstContext -> Elem -> Mb Elem
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

  public export
  occursNu : Signature -> Omega -> Elem -> OmegaName -> M Bool
  occursNu sig omega (PiTy x dom cod) k =
    occurs sig omega dom k `or` occurs sig omega cod k
  occursNu sig omega (PiVal x dom cod f) k =
    occurs sig omega dom k `or` occurs sig omega cod k `or` occurs sig omega f k
  occursNu sig omega (PiElim f x dom cod e) k =
    occurs sig omega f k `or` occurs sig omega dom k `or` occurs sig omega cod k `or` occurs sig omega e k
  occursNu sig omega Universe k = return False
  occursNu sig omega NatVal0 k = return False
  occursNu sig omega (NatVal1 t) k = occurs sig omega t k
  occursNu sig omega NatTy k = return False
  occursNu sig omega (NatElim x schema z y h s t) k =
    occurs sig omega schema k `or` occurs sig omega z k `or` occurs sig omega s k `or` occurs sig omega t k
  occursNu sig omega (ContextSubstElim x y) k = assert_total $ idris_crash "occursNu(ContextSubstElim)"
  occursNu sig omega (SignatureSubstElim x y) k = assert_total $ idris_crash "occursNu(SignatureSubstElim)"
  occursNu sig omega (ContextVarElim j) k = return False
  occursNu sig omega (SignatureVarElim j sigma) k = occurs sig omega sigma k
  occursNu sig omega (OmegaVarElim j sigma) k = return (j == k) `or` occurs sig omega sigma k
  occursNu sig omega (EqTy a b ty) k = occurs sig omega a k `or` occurs sig omega b k `or` occurs sig omega ty k
  occursNu sig omega EqVal k = return False

  public export
  occurs : Signature -> Omega -> Elem -> OmegaName -> M Bool
  occurs sig omega t k = occursNu sig omega !(openEval sig omega t) k

||| Σ Ω Γ ⊦ ? σ ~ t : A
public export
trySolveElem : Signature -> Omega -> Context -> OmegaName -> Context -> Elem -> SubstContext -> Elem -> Elem -> M Result
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
  return (Success [] [(holeIdx, rhs')])

||| Σ Ω Γ ⊦ ? σ ~ A type
public export
trySolveType : Signature -> Omega -> Context -> OmegaName -> Context -> SubstContext -> Elem -> M Result
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
  return (Success [] [(holeIdx, rhs')])


namespace Elem
  ||| Σ Ω Γ ⊦ a₀ ~ a₁ : A
  ||| A, a₀, a₁ are head-neutral w.r.t. substitution.
  public export
  unifyElemNu : Signature -> Omega -> Context -> Elem -> Elem -> Elem -> M Result
  unifyElemNu sig cs ctx (PiTy x0 dom0 cod0) (PiTy x1 dom1 cod1) ty = FailSt.do
    return (Success [ ElemConstraint ctx dom0 dom1 Universe
                    , ElemConstraint (Ext ctx x0 dom0) cod0 cod1 Universe
                    ]
                    []
           )
  unifyElemNu sig cs ctx (PiTy x0 dom0 cod0) b ty = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "Π vs something else rigid")
      False => return (Stuck "Π vs something else flex")
  unifyElemNu sig cs ctx (PiVal x0 dom0 cod0 f0) (PiVal x1 dom1 cod1 f1) ty = FailSt.do
    return (Success [ ElemConstraint ctx dom0 dom1 Universe
                    , ElemConstraint (Ext ctx x0 dom0) cod0 cod1 Universe
                    , ElemConstraint (Ext ctx x0 dom0) f0 f1 cod0
                    ]
                    []
           )
  unifyElemNu sig cs ctx (PiVal x0 a0 b0 f0) b ty = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "λ vs something else rigid")
      False => return (Stuck "λ vs something else flex")
  unifyElemNu sig cs ctx (PiElim f0 x0 dom0 cod0 e0) (PiElim f1 x1 dom1 cod1 e1) ty = M.do
    return (Success [ElemConstraint ctx dom0 dom1 Universe
                    , ElemConstraint (Ext ctx x0 dom0) cod0 cod1 Universe
                    , ElemConstraint ctx f0 f1 (PiTy x0 dom0 cod0)
                    , ElemConstraint ctx e0 e1 dom0
                    ]
                    []
           )
  unifyElemNu sig cs ctx (PiElim f0 x0 dom0 cod0 e0) b ty = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "app vs something else rigid")
      False => return (Stuck "app vs something else flex")
  unifyElemNu sig cs ctx Universe Universe ty =
    return (Success [] [])
  unifyElemNu sig cs ctx Universe b ty = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "𝕌 vs something else rigid")
      False => return (Stuck "𝕌 vs something else flex")
  unifyElemNu sig cs ctx NatVal0 NatVal0 ty =
    return (Success [] [])
  unifyElemNu sig cs ctx NatVal0 b ty = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "Z vs something else rigid")
      False => return (Stuck "Z vs something else flex")
  unifyElemNu sig cs ctx (NatVal1 t0) (NatVal1 t1) ty = M.do
    return (Success [ ElemConstraint ctx t0 t1 NatTy] [])
  unifyElemNu sig cs ctx (NatVal1 x) b ty = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "S _ vs something else rigid")
      False => return (Stuck "S _ vs something else flex")
  unifyElemNu sig cs ctx NatTy NatTy ty = return (Success [] [])
  unifyElemNu sig cs ctx NatTy b ty = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "S vs something else rigid")
      False => return (Stuck "S vs something else flex")
  unifyElemNu sig cs ctx (NatElim x0 schema0 z0 y0 h0 s0 t0) (NatElim x1 schema1 z1 y1 h1 s1 t1) ty = M.do
    return (Success [  ElemConstraint (Ext ctx x0 NatTy) schema0 schema1 Universe,
                       ElemConstraint ctx z0 z1 (ContextSubstElim schema0 (Ext Id NatVal0)),
                       ElemConstraint (Ext (Ext ctx y0 NatTy) h0 schema0) s0 s1 (ContextSubstElim schema0 (Ext (WkN 2) (NatVal1 (VarN 1)))),
                       ElemConstraint ctx t0 t1 NatTy] [])

  unifyElemNu sig cs ctx (NatElim x0 schema0 z0 y0 h0 s0 t0) b ty = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "ℕ-elim vs something else rigid")
      False => return (Stuck "ℕ-elim vs something else flex")
  unifyElemNu sig cs ctx (ContextSubstElim x y) b ty = assert_total $ idris_crash "unifyElemNu(ContextSubstElim)"
  unifyElemNu sig cs ctx (SignatureSubstElim x y) b ty = assert_total $ idris_crash "unifyElemNu(SignatureSubstElim)"
  unifyElemNu sig cs ctx (ContextVarElim k0) (ContextVarElim k1) ty = M.do
    case k0 == k1 of
      True => return (Success [] [])
      False => return (Disunifier "xᵢ vs xⱼ where i ≠ j")
  unifyElemNu sig cs ctx (ContextVarElim k) b ty = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "xᵢ vs something else rigid")
      False => return (Stuck "xᵢ vs something else flex")
  unifyElemNu sig cs ctx (EqTy p0 q0 ty0) (EqTy p1 q1 ty1) _ = M.do
    return (Success [  ElemConstraint ctx ty0 ty1 Universe,
                       ElemConstraint ctx p0 p1 ty0,
                       ElemConstraint ctx q0 q1 ty0] [])
  unifyElemNu sig cs ctx (EqTy p0 q0 ty0) b _ = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "(≡) vs something else rigid")
      False => return (Stuck "(≡) vs something else flex")
  unifyElemNu sig cs ctx EqVal EqVal ty = return (Success [] [])
  unifyElemNu sig cs ctx EqVal b ty = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "* vs something else rigid")
      False => return (Stuck "* vs something else flex")
  unifyElemNu sig cs ctx (SignatureVarElim k0 sigma0) (SignatureVarElim k1 sigma1) ty = M.do
    case (k0 == k1) of
      False => return (Disunifier "χᵢ vs χⱼ where i ≠ j")
      True =>
        return (Success [ SubstContextConstraint sigma0 sigma1 ctx (getCtx k0)] [])
       where
        getCtx : Nat -> Context
        getCtx k =
          case (splitAt sig k) of
            Nothing => assert_total $ idris_crash "invertNu(SignatureVarElim)(1)"
            Just (_, (_, e), rest) =>
              case subst e (WkN $ 1 + length rest) of
               CtxEntry => assert_total $ idris_crash "invertNu(SignatureVarElim)(2)"
               TypeEntry xi => xi
               ElemEntry xi {} => xi
               LetElemEntry xi {} => xi
               EqTyEntry {} => assert_total $ idris_crash "invertNu(SignatureVarElim)(3)"
  unifyElemNu sig cs ctx (SignatureVarElim k0 sigma0) b ty = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "χᵢ vs something else rigid")
      False => return (Stuck "χᵢ vs something else flex")
  unifyElemNu sig cs ctx a@(OmegaVarElim k0 sigma0) b@(OmegaVarElim k1 sigma1) ty = M.do
    let Just entry0 = lookup k0 cs
         | _ => assert_total $ idris_crash "unifyElemNu(OmegaVarElim(1))"
    let Just entry1 = lookup k1 cs
         | _ => assert_total $ idris_crash "unifyElemNu(OmegaVarElim(2))"
    case (entry0, entry1) of
      -- Both sides are holes, try solving for each side.
      (MetaElem hctx0 hty0 SolveByUnification, MetaElem hctx1 hty1 SolveByUnification) =>
         case !(trySolveElem sig cs ctx k0 hctx0 hty0 sigma0 b ty) of
           Success cs sols => return (Success cs sols)
           Stuck _ => trySolveElem sig cs ctx k1 hctx1 hty1 sigma1 a ty
           Disunifier dis => return (Disunifier dis)
      -- One side is a hole
      (MetaElem hctx0 hty0 SolveByUnification, _) =>
        trySolveElem sig cs ctx k0 hctx0 hty0 sigma0 b ty
      -- One side is a hole
      (_, MetaElem hctx1 hty1 SolveByUnification) =>
        trySolveElem sig cs ctx k1 hctx1 hty1 sigma1 a ty
      -- Both sides are rigid
      (e, _) =>
        case (k0 == k1) of
          False => return (Disunifier "χᵢ vs χⱼ, where i ≠ j")
          True =>
            case e of
              LetElem target {} => return (Success [ SubstContextConstraint sigma0 sigma1 ctx target] [])
              _ => assert_total $ idris_crash "unifyElemNu(SignatureVarElim, SignatureVarElim)(1)"
  unifyElemNu sig cs ctx a@(OmegaVarElim k sigma) b ty = M.do
    -- we now that b is rigid here
    case !(isRigid sig cs a) of
      True => return (Disunifier "rigid χᵢ vs something else rigid")
      False => M.do
       let Just entry = lookup k cs
            | _ => assert_total $ idris_crash "unifyElemNu(SignatureVarElim(3))"
       case entry of
         -- We've got a hole, try solving it
         MetaElem hctx hty SolveByUnification => trySolveElem sig cs ctx k hctx hty sigma b ty
         -- We've got something rigid, that's a disunifier
         _ => return (Disunifier "? vs something else rigid")

  public export
  unifyElem : Signature -> Omega -> Context -> Elem -> Elem -> Elem -> M Result
  unifyElem sig cs ctx a b ty = unifyElemNu sig cs ctx !(openEval sig cs a) !(openEval sig cs b) !(openEval sig cs ty)

namespace Type'
  ||| Σ Ω Γ ⊦ A₀ ~ A₁ type
  ||| A₀ and A₁ are head-neutral w.r.t. substitution.
  public export
  unifyTypeNu : Signature -> Omega -> Context -> Elem -> Elem -> M Result
  unifyTypeNu sig cs ctx (PiTy x0 dom0 cod0) (PiTy x1 dom1 cod1) = FailSt.do
    return (Success [ ElemConstraint ctx dom0 dom1 Universe
                    , ElemConstraint (Ext ctx x0 dom0) cod0 cod1 Universe
                    ]
                    []
           )
  unifyTypeNu sig cs ctx (PiTy x0 dom0 cod0) b = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "Π vs something else rigid")
      False => return (Stuck "Π vs something else flex")
  unifyTypeNu sig cs ctx Universe Universe =
    return (Success [] [])
  unifyTypeNu sig cs ctx Universe b = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "𝕌 vs something else rigid")
      False => return (Stuck "𝕌 vs something else flex")
  unifyTypeNu sig cs ctx NatTy NatTy = return (Success [] [])
  unifyTypeNu sig cs ctx NatTy b = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "S vs something else rigid")
      False => return (Stuck "S vs something else flex")
  unifyTypeNu sig cs ctx (ContextSubstElim x y) b = assert_total $ idris_crash "unifyTypeNu(ContextSubstElim)"
  unifyTypeNu sig cs ctx (SignatureSubstElim x y) b = assert_total $ idris_crash "unifyTypeNu(SignatureSubstElim)"
  unifyTypeNu sig cs ctx (EqTy p0 q0 ty0) (EqTy p1 q1 ty1) = M.do
    return (Success [  ElemConstraint ctx ty0 ty1 Universe,
                       ElemConstraint ctx p0 p1 ty0,
                       ElemConstraint ctx q0 q1 ty0] [])
  unifyTypeNu sig cs ctx (EqTy p0 q0 ty0) b = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "(≡) vs something else rigid")
      False => return (Stuck "(≡) vs something else flex")
  unifyTypeNu sig cs ctx (SignatureVarElim k0 sigma0) (SignatureVarElim k1 sigma1) = M.do
    case (k0 == k1) of
      False => return (Disunifier "χᵢ vs χⱼ where i ≠ j")
      True =>
        return (Success [ SubstContextConstraint sigma0 sigma1 ctx (getCtx k0)] [])
       where
        getCtx : Nat -> Context
        getCtx k =
          case (splitAt sig k) of
            Nothing => assert_total $ idris_crash "invertNu(SignatureVarElim)(1)"
            Just (_, (_, e), rest) =>
              case subst e (WkN $ 1 + length rest) of
               CtxEntry => assert_total $ idris_crash "invertNu(SignatureVarElim)(2)"
               TypeEntry xi => xi
               ElemEntry xi {} => xi
               LetElemEntry xi {} => xi
               EqTyEntry {} => assert_total $ idris_crash "invertNu(SignatureVarElim)(3)"
  unifyTypeNu sig cs ctx (SignatureVarElim k0 sigma0) b = M.do
    case !(isRigid sig cs b) of
      True => return (Disunifier "χᵢ vs something else rigid")
      False => return (Stuck "χᵢ vs something else flex")
  unifyTypeNu sig cs ctx a@(OmegaVarElim k0 sigma0) b@(OmegaVarElim k1 sigma1) = M.do
    let Just entry0 = lookup k0 cs
         | _ => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim(1))"
    let Just entry1 = lookup k1 cs
         | _ => assert_total $ idris_crash "unifyTypeNu(OmegaVarElim(2))"
    case (entry0, entry1) of
      -- Both sides are holes, try solving for each side.
      (MetaType hctx0 SolveByUnification, MetaType hctx1 SolveByUnification) =>
         case !(trySolveType sig cs ctx k0 hctx0 sigma0 b) of
           Success cs sols => return (Success cs sols)
           Stuck _ => trySolveType sig cs ctx k1 hctx1 sigma1 a
           Disunifier dis => return (Disunifier dis)
      -- One side is a hole
      (MetaType hctx0 SolveByUnification, _) =>
        trySolveType sig cs ctx k0 hctx0 sigma0 b
      -- One side is a hole
      (_, MetaType hctx1 SolveByUnification) =>
        trySolveType sig cs ctx k1 hctx1 sigma1 a
      -- Both sides are rigid
      (e, _) =>
        case (k0 == k1) of
          False => return (Disunifier "χᵢ vs χⱼ, where i ≠ j")
          True =>
            case e of
              LetType target {} => return (Success [ SubstContextConstraint sigma0 sigma1 ctx target] [])
              _ => assert_total $ idris_crash "unifyTypeNu(SignatureVarElim, SignatureVarElim)(1)"
  unifyTypeNu sig cs ctx a@(OmegaVarElim k sigma) b = M.do
    -- we now that b is rigid here
    case !(isRigid sig cs a) of
      True => return (Disunifier "rigid χᵢ vs something else rigid")
      False => M.do
       let Just entry = lookup k cs
            | _ => assert_total $ idris_crash "unifyTypeNu(SignatureVarElim(3))"
       case entry of
         -- We've got a hole, try solving it
         MetaType hctx SolveByUnification => trySolveType sig cs ctx k hctx sigma b
         -- We've got something rigid, that's a disunifier
         _ => return (Disunifier "? vs something else rigid")
  unifyTypeNu sig cs ctx _ _ = assert_total $ idris_crash "unifyTypeNu"

  public export
  unifyType : Signature -> Omega -> Context -> Elem -> Elem -> M Result
  unifyType sig cs ctx a b = unifyTypeNu sig cs ctx !(openEval sig cs a) !(openEval sig cs b)

namespace SubstContextNF
  public export
  unify : Signature -> Omega -> SubstContextNF -> SubstContextNF -> Context -> Context -> M Result
  unify sig cs Terminal b source target = return (Success [] [])
  unify sig cs (WkN k) Terminal source target = return (Success [] [])
  unify sig cs (WkN k) (WkN j) source target =
    case (k == j) of
      True => return (Success [] [])
      False => return (Disunifier "↑ⁱ vs iᵏ where i ≠ k")
  unify sig cs (WkN k) (Ext sigma t) source (Ext target x ty) =
    return (Success [  SubstContextConstraint sigma (WkN (S k)) source target,
                       ElemConstraint source t (ContextVarElim k) (ContextSubstElim ty sigma)] [])
  unify sig cs (WkN k) (Ext sigma t) source target = return (Stuck "↑ⁿ vs (_, _) where the target context is not an extension")
  unify sig cs (Ext x y) Terminal source target = return (Success [] [])
  unify sig cs (Ext sigma t) (WkN k) source (Ext target x ty) =
    return (Success [  SubstContextConstraint sigma (WkN (S k)) source target,
                       ElemConstraint source t (ContextVarElim k) (ContextSubstElim ty sigma)] [])
  unify sig cs (Ext sigma t) (WkN k) source target = return (Stuck "↑ⁿ vs (_, _) where the target context is not an extension")
  unify sig cs (Ext sigma p) (Ext tau q) source (Ext target x ty) =
    return (Success [  SubstContextConstraint sigma tau source target,
                       ElemConstraint source p q (ContextSubstElim ty sigma)] [])
  unify sig cs (Ext sigma p) (Ext tau q) source target = return (Stuck "(_, _) vs (_, _) where the target context is not an extension")

namespace SubstContext
  -- Ext σ t ~ Ext σ' t' : Γ ⇒ Δ (x : A) <=> (σ = σ' : Γ ⇒ Δ) ^ (Γ ⊦ t ~ t' : A(σ))
  -- Terminal ~ _ <=> 𝟙
  -- Ext σ t ~ Wk k : Γ ⇒ Δ (x : A) <=> (σ ~ Wk (S k) : Γ ⇒ Δ) ^ (Γ ⊦ t ~ Var k : A(σ))
  -- (Wk k ~ Wk n : _) <=> k = n
  public export
  unifySubstContext : Signature -> Omega -> SubstContext -> SubstContext -> Context -> Context -> M Result
  unifySubstContext sig cs a b source target = unify sig cs (eval a) (eval b) source target

namespace ConstraintEntry
  public export
  unify : Signature -> Omega -> ConstraintEntry -> M Result
  unify sig cs (TypeConstraint ctx a b) = unifyType sig cs ctx a b
  unify sig cs (ElemConstraint ctx a b ty) = unifyElem sig cs ctx a b ty
  unify sig cs (SubstContextConstraint sigma tau source target) = unifySubstContext sig cs sigma tau source target

public export
instantiate : Omega -> OmegaName -> Elem -> Omega
instantiate omega idx rhs =
  case (lookup idx omega) of
    Just (MetaElem ctx ty SolveByUnification) => insert (idx, LetElem ctx rhs ty) omega
    Just (MetaType ctx SolveByUnification) => insert (idx, LetType ctx rhs) omega
    _ => assert_total $ idris_crash "instantiate"

public export
instantiateN : Omega -> List (OmegaName, Elem) -> Omega
instantiateN sig [] = sig
instantiateN sig ((idx, rhs) :: rest) = instantiateN (instantiate sig idx rhs) rest

public export
addConstraint : Omega -> ConstraintEntry -> UnifyM Omega
addConstraint omega e = M.do
  x <- nextOmegaName
  return $ insert (x, toOmegaEntry e) omega

public export
newTypeMeta : Omega -> Context -> MetaKind -> UnifyM (Omega, OmegaName)
newTypeMeta omega ctx k = M.do
  n <- nextOmegaName
  return (insert (n, MetaType ctx k) omega, n)

public export
newElemMeta : Omega -> Context -> Elem -> MetaKind -> UnifyM (Omega, OmegaName)
newElemMeta omega ctx ty k = M.do
  n <- nextOmegaName
  return (insert (n, MetaElem ctx ty k) omega, n)

public export
addConstraintN : Omega -> List ConstraintEntry -> UnifyM Omega
addConstraintN omega [] = return omega
addConstraintN omega (e :: es) = addConstraintN !(addConstraint omega e) es

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
progressEntry sig cs e =
  case !(liftM $ unify sig cs e) of
    Success new is => M.do
      let cs = instantiateN cs is
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
    ||| We've haven't progressed at all.
    Stuck : String -> Progress2
    ||| Ω ≃ ⊥ // The list of constraints is contradictive.
    Disunifier : String -> Progress2

||| Try solving the constraints in the list by passing through it once.
progressEntries : Signature
               -> (omega : Omega)
               -> List ConstraintEntry
               -> Bool
               -> UnifyM Progress2
progressEntries sig cs [] False = return (Stuck "No progress made")
progressEntries sig cs [] True = return (Success cs)
progressEntries sig cs (e :: es) progressMade =
  case !(progressEntry sig cs e) of
    Success cs' new => progressEntries sig cs' (new <>> es) True
    Stuck str => progressEntries sig !(addConstraint cs e) es progressMade
    Disunifier str => return (Disunifier str)

namespace Fixpoint
  ||| The end-product of solving a list of constraints
  public export
  data Fixpoint : Type where
    ||| We've solved all constraints.
    Success : Omega -> Fixpoint
    ||| Some constraints are left unsolved and we can't make a single step forward.
    Stuck : String -> Fixpoint
    ||| Ω ≃ ⊥ // The list of constraints is contradictive.
    Disunifier : String -> Fixpoint

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

||| Try solving the constraints in the list until either no constraints are left or each and every one is stuck.
progressEntriesFixpoint : Signature -> Omega -> List ConstraintEntry -> UnifyM Fixpoint
progressEntriesFixpoint sig cs todo = M.do
  case !(progressEntries sig cs todo False) of
    Stuck str => return (Stuck str)
    Disunifier str => return (Disunifier str)
    Success cs' =>
      case (getConstraints cs') of
        [] => return (Success cs')
        todo => progressEntriesFixpoint sig (onlyMetas cs') todo

public export
solve : Signature -> Omega -> UnifyM Fixpoint
solve sig cs = progressEntriesFixpoint sig (onlyMetas cs) (getConstraints cs)
