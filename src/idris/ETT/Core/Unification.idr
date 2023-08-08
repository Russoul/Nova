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

namespace Result
  ||| Unification step result while solving a constraint.
  public export
  data Result : Type where
    ||| A step has been made.
    Success : Constraints -> (sols : List (Nat, Elem)) -> Result
    ||| A step has *not* been made.
    Stuck : String -> Result
    ||| Constraint is contradictive.
    Disunifier : String -> Result

||| A term head-neutral w.r.t. substitution is rigid if
||| there is no (~) that changes its constructor.
public export
isRigid : Signature -> Elem -> M Bool
isRigid sig (PiTy str x y) = return True
isRigid sig (PiVal str x y z) = return True
isRigid sig (PiElim x str y z w) = return True
isRigid sig Universe = return True
isRigid sig NatVal0 = return True
isRigid sig (NatVal1 x) = return True
isRigid sig NatTy = return True
isRigid sig (NatElim str x y str1 str2 z w) = return True
isRigid sig (ContextSubstElim x y) = assert_total $ idris_crash "isRigid(ContextSubstElim)"
isRigid sig (SignatureSubstElim x y) = assert_total $ idris_crash "isRigid(SignatureSubstElim)"
isRigid sig (ContextVarElim k) = M.do
  let Just (_, (x, entry), _) = splitAt sig k
    | Nothing => assert_total $ idris_crash "isRigid(ContextVarElim)"
  case entry of
    ElemEntry _ _ True => return False
    _ => return True
isRigid sig (SignatureVarElim k x) = return True
isRigid sig (EqTy x y z) = return True
isRigid sig EqVal = return True

mutual
  namespace SubstContextNF
    -- σ : Γ ⇒ Δ
    -- τ : Γ ⇒ Ω
    -- ? : Δ ⇒ Ω such that ? ∘ σ ~ τ
    --
    public export
    invert : Signature
          -> (sigma : SubstContext)
          -> (tau : SubstContextNF)
          -> (gamma : Context)
          -> (delta : Context)
          -> (omega : Context)
          -> Mb SubstContext
    invert sig sigma Terminal gamma delta omega = Mb.do return Terminal
    -- σ : Γ₀ Γ₁ ⇒ Δ
    -- ↑(Γ₁) : Γ₀ Γ₁ ⇒ Γ₀
    -- ? : Δ ⇒ Γ₀ such that ? ∘ σ ~ ↑(Γ₁)
    --
    -- in that case ↑ᵏ = ·
    invert sig sigma (WkN k) gamma delta Empty = Mb.do return Terminal
    -- in that case ↑ᵏ = (↑ᵏ⁺¹, k)
    invert sig sigma (WkN k) gamma delta omega@(Ext _ _ _) =
      SubstContextNF.invert sig sigma (Ext (WkN (S k)) (ContextVarElim k)) gamma delta omega
    -- TODO: IDK how to find the inverse in that case:
    invert sig sigma (WkN k) gamma delta (SignatureVarElim j) = nothing
    invert sig sigma (Ext tau t) gamma delta (Ext omega {}) = Mb.do
      tau' <- invert sig sigma tau gamma delta omega
      t' <- invert sig gamma delta sigma t
      return (Ext tau' t')
    invert sig sigma (Ext tau t) gamma delta _ = Mb.do
      assert_total $ idris_crash "SubstContextNF.invert(Ext)"

  namespace SubstContext
    -- σ : Γ ⇒ Δ
    -- τ : Γ ⇒ Ω
    -- ? : Δ ⇒ Ω such that ? ∘ σ ~ τ
    --
    public export
    invert : Signature
          -> (sigma : SubstContext)
          -> (tau : SubstContext)
          -> (gamma : Context)
          -> (delta : Context)
          -> (omega : Context)
          -> Mb SubstContext
    invert sig sigma tau = invert sig sigma (eval tau)

  namespace Elem
    -- Substitution x̄ can only be a mixture of permutation and deletition.
    -- Then solution for y:
    -- y(x̄) = x
    -- is unique if it exists.
    -- Γ ⊦ t
    -- σ : Γ ⇒ Δ
    public export
    invertNu : Signature -> (gamma : Context) -> (delta : Context) -> (sigma : SubstContext) -> (t : Elem) -> Mb Elem
    invertNu sig ctx delta sigma (PiTy x dom cod) = Mb.do
      dom' <- invert sig ctx delta sigma dom
      cod' <- invert sig (Ext ctx x dom) (Ext delta x dom') (Under sigma) cod
      return (PiTy x dom' cod')
    invertNu sig ctx delta sigma (PiVal x dom cod f) = Mb.do
      dom' <- invert sig ctx delta sigma dom
      cod' <- invert sig (Ext ctx x dom) (Ext delta x dom') (Under sigma) cod
      f' <- invert sig (Ext ctx x dom) (Ext delta x dom') (Under sigma) f
      return (PiVal x dom' cod' f')
    invertNu sig ctx delta sigma (PiElim f x dom cod e) = Mb.do
      f' <- invert sig ctx delta sigma f
      dom' <- invert sig ctx delta sigma dom
      cod' <- invert sig (Ext ctx x dom) (Ext delta x dom') (Under sigma) cod
      e' <- invert sig ctx delta sigma e
      return (PiElim f' x dom' cod' e')
    invertNu sig ctx delta sigma Universe = Mb.do return Universe
    invertNu sig ctx delta sigma NatVal0 = Mb.do return NatVal0
    invertNu sig ctx delta sigma (NatVal1 t) = Mb.do
      t <- invert sig ctx delta sigma t
      return (NatVal1 t)
    invertNu sig ctx delta sigma NatTy = Mb.do return NatTy
    invertNu sig ctx delta sigma (NatElim x schema z y h s t) = Mb.do
      schema' <- invert sig (Ext ctx x NatTy) (Ext delta x NatTy) (Under sigma) schema
      z' <- invert sig ctx delta sigma z
      s' <- invert sig (Ext (Ext ctx y NatTy) h schema) (Ext (Ext delta y NatTy) h schema') (Under (Under sigma)) s
      t' <- invert sig ctx delta sigma t
      return (NatElim x schema' z' y h s' t')
    invertNu sig ctx delta sigma (ContextSubstElim x y) = assert_total $ idris_crash "invertNu(ContextSubstElim)"
    invertNu sig ctx delta sigma (SignatureSubstElim x y) = assert_total $ idris_crash "invertNu(SignatureSubstElim)"
    invertNu sig ctx delta sigma (ContextVarElim k) = Mb.do
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
          case !(liftM $ openEval sig t) of
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
    invertNu sig ctx delta sigma (SignatureVarElim k tau) = Mb.do
      tau' <- invert sig sigma tau ctx delta getOmega
      return (SignatureVarElim k tau')
     where
      getOmega : Context
      getOmega =
        case (splitAt sig k) of
          Nothing => assert_total $ idris_crash "invertNu(SignatureVarElim)(1)"
          Just (_, (_, e), rest) =>
            case subst e (WkN $ 1 + length rest) of
             CtxEntry => assert_total $ idris_crash "invertNu(SignatureVarElim)(2)"
             TypeEntry omega => omega
             ElemEntry omega {} => omega
             LetElemEntry omega {} => omega
             EqTyEntry {} => assert_total $ idris_crash "invertNu(SignatureVarElim)(3)"
    invertNu sig ctx delta sigma (EqTy a b ty) = Mb.do
      a <- invert sig ctx delta sigma a
      b <- invert sig ctx delta sigma b
      ty <- invert sig ctx delta sigma ty
      return (EqTy a b ty)
    invertNu sig ctx delta sigma EqVal = Mb.do return EqVal

    public export
    invert : Signature -> Context -> Context -> SubstContext -> Elem -> Mb Elem
    invert sig ctx delta sigma tm = invertNu sig ctx delta sigma !(liftM $ openEval sig tm)

mutual
  public export
  preinvertibleNu : Signature -> SubstContextNF -> Set Nat -> M Bool
  preinvertibleNu sig Terminal vars = return True
  preinvertibleNu sig (WkN k) vars = return True
  preinvertibleNu sig (Ext sigma t) vars = M.do
    case !(openEval sig t) of
      ContextVarElim k => M.do
        return (not $ isElem k vars) `and` preinvertible sig sigma (insert k vars)
      _ => return False

  ||| Substitution is pre-invertible if
  ||| it consists of permutations and deletions of variables (up to (~)).
  public export
  preinvertible : Signature -> SubstContext -> Set Nat -> M Bool
  preinvertible sig sigma vars = preinvertibleNu sig (eval sigma) vars

mutual
  namespace SubstContextNF
    public export
    occurs : Signature -> SubstContextNF -> Nat -> M Bool
    occurs sig Terminal k = return False
    occurs sig (WkN j) k = return False
    occurs sig (Ext sigma t) k = occurs sig sigma k `or` occurs sig t k

  namespace SubstContext
    public export
    occurs : Signature -> SubstContext -> Nat -> M Bool
    occurs sig sigma k = occurs sig (eval sigma) k

  public export
  occursNu : Signature -> Elem -> Nat -> M Bool
  occursNu sig (PiTy x dom cod) k =
    occurs sig dom k `or` occurs sig cod k
  occursNu sig (PiVal x dom cod f) k =
    occurs sig dom k `or` occurs sig cod k `or` occurs sig f k
  occursNu sig (PiElim f x dom cod e) k =
    occurs sig f k `or` occurs sig dom k `or` occurs sig cod k `or` occurs sig e k
  occursNu sig Universe k = return False
  occursNu sig NatVal0 k = return False
  occursNu sig (NatVal1 t) k = occurs sig t k
  occursNu sig NatTy k = return False
  occursNu sig (NatElim x schema z y h s t) k =
    occurs sig schema k `or` occurs sig z k `or` occurs sig s k `or` occurs sig t k
  occursNu sig (ContextSubstElim x y) k = assert_total $ idris_crash "occursNu(ContextSubstElim)"
  occursNu sig (SignatureSubstElim x y) k = assert_total $ idris_crash "occursNu(SignatureSubstElim)"
  occursNu sig (ContextVarElim j) k = return False
  occursNu sig (SignatureVarElim j sigma) k = return (j == k) `or` occurs sig sigma k
  occursNu sig (EqTy a b ty) k = occurs sig a k `or` occurs sig b k `or` occurs sig ty k
  occursNu sig EqVal k = return False

  public export
  occurs : Signature -> Elem -> Nat -> M Bool
  occurs sig t k = occursNu sig !(openEval sig t) k

||| Σ Ω Γ ⊦ ? σ ~ t : A
public export
trySolve : Signature -> Constraints -> Context -> Nat -> Context -> Elem -> SubstContext -> Elem -> Elem -> M Result
trySolve sig cs ctx holeIdx holeCtx holeTy sigma rhs ty = M.do
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
  False <- occurs sig rhs holeIdx
    | True => return (Stuck "Occurs check failed") -- TODO: strengthen the check to a disunifier in some cases
  True <- preinvertible sig sigma empty
    | False => return (Stuck "Substitution is not invertible")
  Just rhs' <- invert sig ctx holeCtx sigma rhs
    | Nothing => return (Stuck "Can't invert RHS")
  return (Success [<] [(holeIdx, rhs')])


namespace Elem
  ||| Σ Ω Γ ⊦ a₀ ~ a₁ : A
  ||| A is head-neutral w.r.t. substitution.
  public export
  unifyNu : Signature -> Constraints -> Context -> Elem -> Elem -> Elem -> M Result
  unifyNu sig cs ctx (PiTy x0 dom0 cod0) (PiTy x1 dom1 cod1) ty = FailSt.do
    return (Success [< ElemConstraint ctx dom0 dom1 Universe
                    , ElemConstraint (Ext ctx x0 dom0) cod0 cod1 Universe
                    ]
                    []
           )
  unifyNu sig cs ctx (PiTy x0 dom0 cod0) b ty = M.do
    case !(isRigid sig b) of
      True => return (Disunifier "Π vs something else rigid")
      False => return (Stuck "Π vs something else flex")
  unifyNu sig cs ctx (PiVal x0 dom0 cod0 f0) (PiVal x1 dom1 cod1 f1) ty = FailSt.do
    return (Success [< ElemConstraint ctx dom0 dom1 Universe
                    , ElemConstraint (Ext ctx x0 dom0) cod0 cod1 Universe
                    , ElemConstraint (Ext ctx x0 dom0) f0 f1 cod0
                    ]
                    []
           )
  unifyNu sig cs ctx (PiVal x0 a0 b0 f0) b ty = M.do
    case !(isRigid sig b) of
      True => return (Disunifier "λ vs something else rigid")
      False => return (Stuck "λ vs something else flex")
  unifyNu sig cs ctx (PiElim f0 x0 dom0 cod0 e0) (PiElim f1 x1 dom1 cod1 e1) ty = M.do
    return (Success [< ElemConstraint ctx dom0 dom1 Universe
                    , ElemConstraint (Ext ctx x0 dom0) cod0 cod1 Universe
                    , ElemConstraint ctx f0 f1 (PiTy x0 dom0 cod0)
                    , ElemConstraint ctx e0 e1 dom0
                    ]
                    []
           )
  unifyNu sig cs ctx (PiElim f0 x0 dom0 cod0 e0) b ty = M.do
    case !(isRigid sig b) of
      True => return (Disunifier "app vs something else rigid")
      False => return (Stuck "app vs something else flex")
  unifyNu sig cs ctx Universe Universe ty =
    return (Success [<] [])
  unifyNu sig cs ctx Universe b ty = M.do
    case !(isRigid sig b) of
      True => return (Disunifier "𝕌 vs something else rigid")
      False => return (Stuck "𝕌 vs something else flex")
  unifyNu sig cs ctx NatVal0 NatVal0 ty =
    return (Success [<] [])
  unifyNu sig cs ctx NatVal0 b ty = M.do
    case !(isRigid sig b) of
      True => return (Disunifier "Z vs something else rigid")
      False => return (Stuck "Z vs something else flex")
  unifyNu sig cs ctx (NatVal1 t0) (NatVal1 t1) ty = M.do
    return (Success [< ElemConstraint ctx t0 t1 NatTy] [])
  unifyNu sig cs ctx (NatVal1 x) b ty = M.do
    case !(isRigid sig b) of
      True => return (Disunifier "S _ vs something else rigid")
      False => return (Stuck "S _ vs something else flex")
  unifyNu sig cs ctx NatTy NatTy ty = return (Success [<] [])
  unifyNu sig cs ctx NatTy b ty = M.do
    case !(isRigid sig b) of
      True => return (Disunifier "S vs something else rigid")
      False => return (Stuck "S vs something else flex")
  unifyNu sig cs ctx (NatElim x0 schema0 z0 y0 h0 s0 t0) (NatElim x1 schema1 z1 y1 h1 s1 t1) ty = M.do
    return (Success [< ElemConstraint (Ext ctx x0 NatTy) schema0 schema1 Universe,
                       ElemConstraint ctx z0 z1 (ContextSubstElim schema0 (Ext Id NatVal0)),
                       ElemConstraint (Ext (Ext ctx y0 NatTy) h0 schema0) s0 s1 (ContextSubstElim schema0 (Ext (WkN 2) (NatVal1 (VarN 1)))),
                       ElemConstraint ctx t0 t1 NatTy] [])

  unifyNu sig cs ctx (NatElim x0 schema0 z0 y0 h0 s0 t0) b ty = M.do
    case !(isRigid sig b) of
      True => return (Disunifier "ℕ-elim vs something else rigid")
      False => return (Stuck "ℕ-elim vs something else flex")
  unifyNu sig cs ctx (ContextSubstElim x y) b ty = assert_total $ idris_crash "unifyNu(ContextSubstElim)"
  unifyNu sig cs ctx (SignatureSubstElim x y) b ty = assert_total $ idris_crash "unifyNu(SignatureSubstElim)"
  unifyNu sig cs ctx (ContextVarElim k0) (ContextVarElim k1) ty = M.do
    case k0 == k1 of
      True => return (Success [<] [])
      False => return (Disunifier "xᵢ vs xⱼ where i ≠ j")
  unifyNu sig cs ctx (ContextVarElim k) b ty = M.do
    case !(isRigid sig b) of
      True => return (Disunifier "xᵢ vs something else rigid")
      False => return (Stuck "xᵢ vs something else flex")
  unifyNu sig cs ctx (EqTy p0 q0 ty0) (EqTy p1 q1 ty1) _ = M.do
    return (Success [< ElemConstraint ctx ty0 ty1 Universe,
                       ElemConstraint ctx p0 p1 ty0,
                       ElemConstraint ctx q0 q1 ty0] [])
  unifyNu sig cs ctx (EqTy p0 q0 ty0) b _ = M.do
    case !(isRigid sig b) of
      True => return (Disunifier "(≡) vs something else rigid")
      False => return (Stuck "(≡) vs something else flex")
  unifyNu sig cs ctx EqVal EqVal ty = return (Success [<] [])
  unifyNu sig cs ctx EqVal b ty = M.do
    case !(isRigid sig b) of
      True => return (Disunifier "* vs something else rigid")
      False => return (Stuck "* vs something else flex")
  unifyNu sig cs ctx a@(SignatureVarElim k0 sigma0) b@(SignatureVarElim k1 sigma1) ty = M.do
    let Just (_, (_, entry0), rest0) = splitAt sig k0
         | _ => assert_total $ idris_crash "unifyNu(SignatureVarElim(1))"
    let Just (_, (_, entry1), rest1) = splitAt sig k1
         | _ => assert_total $ idris_crash "unifyNu(SignatureVarElim(2))"
    case (subst entry0 (WkN (1 + length rest0)), subst entry1 (WkN (1 + length rest0))) of
      -- Both sides are holes, try solving for each side.
      (ElemEntry hctx0 hty0 True, ElemEntry hctx1 hty1 True) =>
         case !(trySolve sig cs ctx k0 hctx0 hty0 sigma0 b ty) of
           Success cs sols => return (Success cs sols)
           Stuck _ => trySolve sig cs ctx k1 hctx1 hty1 sigma1 a ty
           Disunifier dis => return (Disunifier dis)
      -- One side is a hole
      (ElemEntry hctx0 hty0 True, _) =>
        trySolve sig cs ctx k0 hctx0 hty0 sigma0 b ty
      -- One side is a hole
      (_, ElemEntry hctx1 hty1 True) =>
        trySolve sig cs ctx k1 hctx1 hty1 sigma1 a ty
      -- Both sides are rigid
      (e, _) =>
        case (k0 == k1) of
          False => return (Disunifier "χᵢ vs χⱼ, where i ≠ j")
          True =>
            case e of
              CtxEntry => assert_total $ idris_crash "unifyNu(SignatureVarElim, SignatureVarElim)(1)"
              TypeEntry target => return (Success [< SubstContextConstraint sigma0 sigma1 ctx target] [])
              ElemEntry target {} => return (Success [< SubstContextConstraint sigma0 sigma1 ctx target] [])
              LetElemEntry target {} => return (Success [< SubstContextConstraint sigma0 sigma1 ctx target] [])
              EqTyEntry {} => assert_total $ idris_crash "unifyNu(SignatureVarElim, SignatureVarElim)(2)"
  unifyNu sig cs ctx a@(SignatureVarElim k sigma) b ty = M.do
    -- we now that b is rigid here
    case !(isRigid sig a) of
      True => return (Disunifier "rigid χᵢ vs something else rigid")
      False => M.do
       let Just (_, (x, entry), rest) = splitAt sig k
            | _ => assert_total $ idris_crash "unifyNu(SignatureVarElim(3))"
       case (subst entry (WkN (1 + length rest))) of
         -- We've got a hole, try solving it
         ElemEntry hctx hty True => trySolve sig cs ctx k hctx hty sigma b ty
         -- We've got something rigid, that's a disunifier
         _ => return (Disunifier "? vs something else rigid")
  public export
  unify : Signature -> Constraints -> Context -> Elem -> Elem -> Elem -> M Result
  unify sig cs ctx a b ty = unifyNu sig cs ctx !(openEval sig a) !(openEval sig b) !(openEval sig ty)

namespace SubstContextNF
  public export
  unify : Signature -> Constraints -> SubstContextNF -> SubstContextNF -> Context -> Context -> M Result
  unify sig cs Terminal b source target = return (Success [<] [])
  unify sig cs (WkN k) Terminal source target = return (Success [<] [])
  unify sig cs (WkN k) (WkN j) source target =
    case (k == j) of
      True => return (Success [<] [])
      False => return (Disunifier "↑ⁱ vs iᵏ where i ≠ k")
  unify sig cs (WkN k) (Ext sigma t) source (Ext target x ty) =
    return (Success [< SubstContextConstraint sigma (WkN (S k)) source target,
                       ElemConstraint source t (ContextVarElim k) (ContextSubstElim ty sigma)] [])
  unify sig cs (WkN k) (Ext sigma t) source target = return (Stuck "↑ⁿ vs (_, _) where the target context is not an extension")
  unify sig cs (Ext x y) Terminal source target = return (Success [<] [])
  unify sig cs (Ext sigma t) (WkN k) source (Ext target x ty) =
    return (Success [< SubstContextConstraint sigma (WkN (S k)) source target,
                       ElemConstraint source t (ContextVarElim k) (ContextSubstElim ty sigma)] [])
  unify sig cs (Ext sigma t) (WkN k) source target = return (Stuck "↑ⁿ vs (_, _) where the target context is not an extension")
  unify sig cs (Ext sigma p) (Ext tau q) source (Ext target x ty) =
    return (Success [< SubstContextConstraint sigma tau source target,
                       ElemConstraint source p q (ContextSubstElim ty sigma)] [])
  unify sig cs (Ext sigma p) (Ext tau q) source target = return (Stuck "(_, _) vs (_, _) where the target context is not an extension")

namespace SubstContext
  -- Ext σ t ~ Ext σ' t' : Γ ⇒ Δ (x : A) <=> (σ = σ' : Γ ⇒ Δ) ^ (Γ ⊦ t ~ t' : A(σ))
  -- Terminal ~ _ <=> 𝟙
  -- Ext σ t ~ Wk k : Γ ⇒ Δ (x : A) <=> (σ ~ Wk (S k) : Γ ⇒ Δ) ^ (Γ ⊦ t ~ Var k : A(σ))
  -- (Wk k ~ Wk n : _) <=> k = n
  public export
  unify : Signature -> Constraints -> SubstContext -> SubstContext -> Context -> Context -> M Result
  unify sig cs a b source target = unify sig cs (eval a) (eval b) source target

namespace ConstraintEntry
  public export
  unify : Signature -> Constraints -> ConstraintEntry -> M Result
  unify sig cs (ElemConstraint ctx a b ty) = unify sig cs ctx a b ty
  unify sig cs (SubstContextConstraint sigma tau source target) = unify sig cs sigma tau source target

instantiate : Signature -> Nat -> Elem -> Signature
instantiate sig idx rhs =
  case (splitAt sig idx) of
    Just (before, (x, ElemEntry ctx ty True), after) => before ++ [< (x, LetElemEntry ctx rhs ty True)] ++ after
    _ => assert_total $ idris_crash "instantiate"

instantiateN : Signature -> List (Nat, Elem) -> Signature
instantiateN sig [] = sig
instantiateN sig ((idx, rhs) :: rest) = instantiateN (instantiate sig idx rhs) rest

namespace Progress
  ||| The intermediate results of solving a list of constraints (reflects whether at least some progress has been made).
  public export
  data Progress : Type where
    ||| We've made at least one step in the process of solving constraints.
    Success : Signature -> Constraints -> Progress
    ||| We've haven't progressed at all.
    Stuck : String -> Progress
    ||| Ω ≃ ⊥ // The list of constraints is contradictive.
    Disunifier : String -> Progress

progressEntry : Signature -> Constraints -> ConstraintEntry -> M Progress
progressEntry sig cs e =
  case !(unify sig cs e) of
    Success new is => return (Success (instantiateN sig is) new)
    Stuck str => return (Stuck str)
    Disunifier str => return (Disunifier str)

||| Try solving the constraints in the list by passing through it once.
progressEntries : Signature -> (prefix_ : Constraints) -> (stuck : Constraints) -> List ConstraintEntry -> Bool -> M Progress
progressEntries sig cs stuck [] False = return (Stuck "No progress made")
progressEntries sig cs stuck [] True = return (Success sig stuck)
progressEntries sig cs stuck (e :: es) progressMade =
  case !(progressEntry sig (cs ++ stuck) e) of
    Success sig' new => progressEntries sig' cs stuck (new <>> es) True
    Stuck str => progressEntries sig cs (stuck :< e) es progressMade
    Disunifier str => return (Disunifier str)

namespace Fixpoint
  ||| The end-product of solving a list of constraints
  public export
  data Fixpoint : Type where
    ||| We've solved all constraints.
    Success : Signature -> Fixpoint
    ||| Some constraints are left unsolved and we can't make a single step forward.
    Stuck : String -> Fixpoint
    ||| Ω ≃ ⊥ // The list of constraints is contradictive.
    Disunifier : String -> Fixpoint

||| Try solving the constraints in the list until either no constraints are left or each and every one is stuck.
progressEntriesFixpoint : Signature -> (prefix_ : Constraints) -> List ConstraintEntry -> M Fixpoint
progressEntriesFixpoint sig cs todo = M.do
  case !(progressEntries sig cs [<] todo False) of
    Stuck str => return (Stuck str)
    Disunifier str => return (Disunifier str)
    Success sig' [<] => return (Success sig')
    Success sig' nonEmpty => progressEntriesFixpoint sig cs (cast nonEmpty)

public export
solve : Signature -> Constraints -> M Fixpoint
solve sig cs = progressEntriesFixpoint sig [<] (cast cs)
