module Nova.Surface.Language

import Me.Russoul.Data.Location

import Data.AlternatingList
import Data.AlternatingList1
import Data.Fin
import Data.SnocList
import Data.List1

import Nova.Core.Name
import Nova.Surface.Operator

import Solver.CommutativeMonoid.Language


-- h ::= tt | Z | Refl | x | S | ℕ-elim | 𝟘-elim | J | 𝟘 | 𝟙 | ℕ | 𝕌 | !x | ?x | Π-β | Π-η | Π⁼ | Σ-β₁ | Σ-β₂ | Σ-η | Σ⁼ | 𝟙⁼ | ℕ-β-Z | ℕ-β-S | (e{≥0}) | _ | ☐

-- e{0} = x ↦ e{≥0} | {x} ↦ e{≥0} | (x : e{≥0}) → e{≥0} | {x : e{≥0}} → e{≥0} | (x : e{≥0}) ⨯ e{≥0}
-- e{1} = op e{≥2} op ... e{≥2} op | e{≥2} op e{≥2} ... op e{≥2}
-- e{2} = h ē⁺ where |ē⁺| > 0
-- e{3} = h | (e{≥0}) | \|e{≥0}\|

-- e⁺{0} = x̅.̅ e{≥0}
-- e⁺{1} = e{≥3} | (e⁺{≥0}) | .π₁ | .π₂ | {e{≥0}}
-- ē⁺ ::= ␣ e⁺{1} ē⁺ | ·

-- top-level ::= assume x : e{≥0} | let x : e{≥0} ≔ e{≥0} | define x : e{≥0} ≔ e{≥0} | let-type x ≔ e{≥0} | define-type x ≔ e{≥0}


mutual
  namespace Head
    public export
    data Head : Type where
      Var : Range -> VarName -> Head
      NatVal0 : Range -> Head
      NatVal1 : Range -> Head
      NatElim : Range -> Head
      ZeroElim : Range -> Head
      EqElim : Range -> Head
      EqVal : Range -> Head
      NatTy : Range -> Head
      ZeroTy : Range -> Head
      OneTy : Range -> Head
      OneVal : Range -> Head
      UniverseTy : Range -> Head
      Hole : Range -> VarName -> Maybe (List VarName) -> Head
      UnnamedHole : Range -> Maybe (List VarName) -> Head
      Unfold : Range -> VarName -> Head
      PiBeta : Range -> Head
      PiEta : Range -> Head
      SigmaBeta1 : Range -> Head
      SigmaBeta2 : Range -> Head
      SigmaEta : Range -> Head
      SigmaEq : Range -> Head
      NatBetaZ : Range -> Head
      NatBetaS : Range -> Head
      PiEq : Range -> Head
      OneEq : Range -> Head
      El : Range -> Head
      ||| Only used for paths.
      Underscore : Range -> Head
      ||| Only used for paths.
      Box : Range -> Head
      Tm : Range -> Term -> Head

  namespace OpFreeHead
    public export
    data OpFreeHead : Type where
      Var : Range -> VarName -> OpFreeHead
      NatVal0 : Range -> OpFreeHead
      NatVal1 : Range -> OpFreeHead
      NatElim : Range -> OpFreeHead
      ZeroElim : Range -> OpFreeHead
      EqElim : Range -> OpFreeHead
      EqVal : Range -> OpFreeHead
      NatTy : Range -> OpFreeHead
      ZeroTy : Range -> OpFreeHead
      OneTy : Range -> OpFreeHead
      OneVal : Range -> OpFreeHead
      UniverseTy : Range -> OpFreeHead
      Hole : Range -> VarName -> Maybe (List VarName) -> OpFreeHead
      UnnamedHole : Range -> Maybe (List VarName) -> OpFreeHead
      Unfold : Range -> VarName -> OpFreeHead
      PiBeta : Range -> OpFreeHead
      PiEta : Range -> OpFreeHead
      NatBetaZ : Range -> OpFreeHead
      NatBetaS : Range -> OpFreeHead
      PiEq : Range -> OpFreeHead
      SigmaBeta1 : Range -> OpFreeHead
      SigmaBeta2 : Range -> OpFreeHead
      SigmaEta : Range -> OpFreeHead
      SigmaEq : Range -> OpFreeHead
      OneEq : Range -> OpFreeHead
      El : Range -> OpFreeHead
      ||| Only used for paths.
      Underscore : Range -> OpFreeHead
      ||| Only used for paths.
      Box : Range -> OpFreeHead
      Tm : Range -> OpFreeTerm -> OpFreeHead

  namespace Term
    public export
    data Term : Type where
      PiTy : Range -> List1 VarName -> Term -> Term -> Term
      ImplicitPiTy : Range -> List1 VarName -> Term -> Term -> Term
      SigmaTy : Range -> List1 VarName -> Term -> Term -> Term
      PiVal : Range -> List1 VarName -> Term -> Term
      ImplicitPiVal : Range -> List1 VarName -> Term -> Term
      OpLayer : {k : _} -> Range -> AlternatingList1 k (Range, String) (Range, Head, Elim) -> Term
      InParens : Range -> Term -> Term
      Tac : Range -> Tactic -> Term

  namespace CtxPath
    ||| cᵖ ::= _ (_ : t) _ ... _
    public export
    record CtxPath where
      constructor MkCtxPath
      range : Range
      here : Term
      skipped : Nat

  namespace Tactic
    public export
    data Tactic : Type where
      ||| id
      Id : Range -> Tactic
      ||| α
      ||| β
      Composition : Range -> List1 Tactic -> Tactic
      ||| unfold ρ
      Unfold : Range -> Term -> Tactic
      ||| unfold-ctx cᵖ
      UnfoldCtx : Range -> CtxPath -> Tactic
      ||| exact t
      Exact : Range -> Term -> Tactic
      ||| * α
      ||| * β
      ||| ...
      ||| * γ
      Split : Range -> SnocList Tactic -> Tactic -> Tactic
      Trivial : Range -> Tactic
      ||| rewrite⁻¹ e{≥4} e{≥4}
      RewriteInv : Range -> Term -> Term -> Tactic
      ||| rewrite e{≥4} e{≥4}
      Rewrite : Range -> Term -> Term -> Tactic
      ||| let x ≔ e{≥0}
      Let : Range -> VarName -> Term -> Tactic
      ||| normalise-comm-monoid ρ ω t
      NormaliseCommutativeMonoid : Range
                                -> Term -- vars can't contain duplicates
                                -> (vars : SnocList String ** Term (Fin (length vars)))
                                -> Term
                                -> Tactic

  namespace OpFreeTactic
    public export
    data OpFreeTactic : Type where
      ||| id
      Id : Range -> OpFreeTactic
      ||| α
      ||| β
      Composition : Range -> List1 OpFreeTactic -> OpFreeTactic
      ||| unfold ρ
      Unfold : Range -> OpFreeTerm -> OpFreeTactic
      ||| unfold-ctx ρ
      UnfoldCtx : Range -> OpFreeCtxPath -> OpFreeTactic
      ||| exact t
      Exact : Range -> OpFreeTerm -> OpFreeTactic
      ||| * α
      ||| * β
      ||| ...
      ||| * γ
      Split : Range -> SnocList OpFreeTactic -> OpFreeTactic -> OpFreeTactic
      Trivial : Range -> OpFreeTactic
      ||| rewrite⁻¹ e{≥4} e{≥4}
      RewriteInv : Range -> OpFreeTerm -> OpFreeTerm -> OpFreeTactic
      ||| rewrite e{≥4} e{≥4}
      Rewrite : Range -> OpFreeTerm -> OpFreeTerm -> OpFreeTactic
      ||| let x ≔ t
      Let : Range -> VarName -> OpFreeTerm -> OpFreeTactic
      ||| normalise-comm-monoid ρ ω t
      NormaliseCommutativeMonoid : Range
                                -> OpFreeTerm
                                -> (vars : SnocList String ** Term (Fin (length vars)))
                                -> OpFreeTerm
                                -> OpFreeTactic

  namespace OpFreeTerm
    public export
    data OpFreeTerm : Type where
      PiTy : Range -> VarName -> OpFreeTerm -> OpFreeTerm -> OpFreeTerm
      ImplicitPiTy : Range -> VarName -> OpFreeTerm -> OpFreeTerm -> OpFreeTerm
      SigmaTy : Range -> VarName -> OpFreeTerm -> OpFreeTerm -> OpFreeTerm
      PiVal : Range -> VarName -> OpFreeTerm -> OpFreeTerm
      ImplicitPiVal : Range -> VarName -> OpFreeTerm -> OpFreeTerm
      ProdTy : Range -> OpFreeTerm -> OpFreeTerm -> OpFreeTerm
      FunTy : Range -> OpFreeTerm -> OpFreeTerm -> OpFreeTerm
      TyEqTy : Range -> OpFreeTerm -> OpFreeTerm -> OpFreeTerm
      ElEqTy : Range -> OpFreeTerm -> OpFreeTerm -> OpFreeTerm -> OpFreeTerm
      SigmaVal : Range -> OpFreeTerm -> OpFreeTerm -> OpFreeTerm
      App : Range -> OpFreeHead -> OpFreeElim -> OpFreeTerm
      Tac : Range -> OpFreeTactic -> OpFreeTerm

  namespace OpFreeCtxPath
    public export
    record OpFreeCtxPath where
      constructor MkOpFreeCtxPath
      range : Range
      here : OpFreeTerm
      skipped : Nat

  public export
  TermArg : Type
  TermArg = (List VarName, Term)

  public export
  OpFreeTermArg : Type
  OpFreeTermArg = (List VarName, OpFreeTerm)

  namespace ElimEntry
    public export
    data ElimEntry : Type where
      Arg : TermArg -> ElimEntry
      Pi1 : ElimEntry
      Pi2 : ElimEntry
      ImplicitArg : Term -> ElimEntry

  namespace OpFreeElimEntry
    public export
    data OpFreeElimEntry : Type where
      Arg : OpFreeTermArg -> OpFreeElimEntry
      Pi1 : OpFreeElimEntry
      Pi2 : OpFreeElimEntry
      ImplicitArg : OpFreeTerm -> OpFreeElimEntry

  public export
  Elim : Type
  Elim = List (Range, ElimEntry)

  public export
  OpFreeElim : Type
  OpFreeElim = List (Range, OpFreeElimEntry)

public export
range : Term -> Range
range (PiTy r str y z) = r
range (ImplicitPiTy r str y z) = r
range (SigmaTy r str y z) = r
range (PiVal r str y) = r
range (ImplicitPiVal r str y) = r
range (OpLayer r ls) = r
range (Tac r _) = r
range (InParens r _) = r

mutual
  covering
  public export
  Show ElimEntry where
    show (Arg arg) = "Arg(\{show arg})"
    show (ImplicitArg arg) = "ImplicitArg(\{show arg})"
    show Pi1 = ".π₁"
    show Pi2 = ".π₂"

  public export
  covering
  Show Head where
    show (PiBeta _) = "Π-β"
    show (PiEta _) = "Π-η"
    show (NatBetaZ _) = "ℕ-β-Z"
    show (NatBetaS _) = "ℕ-β-S"
    show (Unfold _ x) = "Unfold(\{x})"
    show (Hole _ x ls) = "Hole(\{x}, \{show ls})"
    show (UnnamedHole _ ls) = "UnnamedHole(\{show ls})"
    show (Var _ x) = "Var(\{x})"
    show (NatVal0 x) = "Z"
    show (NatVal1 x) = "S"
    show (NatElim x) = "ℕ-elim"
    show (ZeroElim x) = "𝟘-elim"
    show (EqElim x) = "J"
    show (EqVal x) = "Refl"
    show (NatTy x) = "ℕ"
    show (ZeroTy x) = "𝟘"
    show (OneTy x) = "𝟙"
    show (OneVal x) = "()"
    show (UniverseTy x) = "𝕌"
    show (PiEq x) = "PiEq"
    show (SigmaBeta1 x) = "SigmaBeta1"
    show (SigmaBeta2 x) = "SigmaBeta2"
    show (SigmaEta x) = "SigmaEta"
    show (SigmaEq x) = "SigmaEq"
    show (OneEq x) = "OneEq"
    show (El x) = "El"
    show (Underscore x) = "_"
    show (Box x) = "☐"
    show (Tm x tm) = "Tm(\{show tm})"

  public export
  covering
  Show Term where
    show (PiTy _ x a b) = "PiTy(\{show a}, \{show b})"
    show (SigmaTy _ x a b) = "SigmaTy(\{show a}, \{show b})"
    show (ImplicitPiTy _ x a b) = "ImplicitPiTy(\{show a}, \{show b})"
    show (PiVal _ x f) = "PiVal(\{show x}, \{show f})"
    show (ImplicitPiVal _ x f) = "ImplicitPiVal(\{show x}, \{show f})"
    show (OpLayer _ list) = "OpLayer(\{show list})"
    show (Tac _ alpha) = "Tac(\{show alpha})"
    show (InParens _ t) = "InParens(\{show t})"

  public export
  covering
  Show CtxPath where
    show (MkCtxPath _ here n) = "CtxPath(\{show here}, \{show n})"

  public export
  covering
  Show Tactic where
    show (Id x) = "Id"
    show (Composition x xs) = "Composition(\{show xs})"
    show (UnfoldCtx x p) = "UnfoldCtx(\{show p})"
    show (Unfold x y) = "Unfold(\{show y})"
    show (Exact x y) = "Exact(\{show y})"
    show (Split x sx y) = "Split(\{show sx}, \{show y})"
    show (Trivial x) = "Trivial"
    show (RewriteInv x y z) = "RewriteInv(\{show y}, \{show z})"
    show (Rewrite x y z) = "Rewrite(\{show y}, \{show z})"
    show (Let x str y) = "Let(\{str}, \{show y})"
    show (NormaliseCommutativeMonoid x y z w) = "NormaliseCommutativeMonoid(...)"

mutual
  covering
  public export
  Show OpFreeElimEntry where
    show (Arg arg) = "Arg(\{show arg})"
    show (ImplicitArg arg) = "ImplicitArg(\{show arg})"
    show Pi1 = ".π₁"
    show Pi2 = ".π₂"

  public export
  covering
  Show OpFreeHead where
    show (PiBeta _) = "Π-β"
    show (PiEta _) = "Π-η"
    show (NatBetaZ _) = "ℕ-β-Z"
    show (NatBetaS _) = "ℕ-β-S"
    show (Unfold _ x) = "Unfold(\{x})"
    show (Hole _ x ls) = "Hole(\{x}, \{show ls})"
    show (UnnamedHole _ ls) = "UnnamedHole(\{show ls})"
    show (Var _ x) = "Var(\{x})"
    show (NatVal0 x) = "Z"
    show (NatVal1 x) = "S"
    show (OneVal x) = "()"
    show (NatElim x) = "ℕ-elim"
    show (ZeroElim x) = "𝟘-elim"
    show (EqElim x) = "J"
    show (EqVal x) = "Refl"
    show (NatTy x) = "ℕ"
    show (ZeroTy x) = "𝟘"
    show (OneTy x) = "𝟙"
    show (UniverseTy x) = "𝕌"
    show (PiEq x) = "PiEq"
    show (SigmaBeta1 x) = "SigmaBeta1"
    show (SigmaBeta2 x) = "SigmaBeta2"
    show (SigmaEta x) = "SigmaEta"
    show (SigmaEq x) = "SigmaEq"
    show (OneEq x) = "OneEq"
    show (El x) = "El"
    show (Underscore x) = "_"
    show (Box x) = "☐"
    show (Tm x tm) = "Tm(\{show tm})"

  public export
  covering
  Show OpFreeTerm where
    show (PiTy _ x a b) = "PiTy(\{show a}, \{show b})"
    show (SigmaTy _ x a b) = "SigmaTy(\{show a}, \{show b})"
    show (ImplicitPiTy _ x a b) = "ImplicitPiTy(\{show a}, \{show b})"
    show (PiVal _ x f) = "PiVal(\{x}, \{show f})"
    show (ImplicitPiVal _ x f) = "ImplicitPiVal(\{x}, \{show f})"
    show (ProdTy _ a b) = "ProdTy(\{show a}, \{show b})"
    show (FunTy _ a b) = "FunTy(\{show a}, \{show b})"
    show (TyEqTy _ a b) = "TyEqTy(\{show a}, \{show b})"
    show (ElEqTy _ a b ty) = "ElEqTy(\{show a}, \{show b}, \{show ty})"
    show (SigmaVal _ a b) = "SigmaVal(\{show a}, \{show b})"
    show (App _ head list) = "App(\{show head}, \{show list})"
    show (Tac _ alpha) = "Tac(...)"

namespace Term
  public export
  data TopLevel : Type where
    ||| assume x : T
    TypingSignature : Range -> VarName -> Term -> TopLevel
    ||| let x : T
    |||       ≔ t
    LetSignature : Range -> VarName -> Term -> Term -> TopLevel
    ||| define x : T
    |||          ≔ t
    DefineSignature : Range -> VarName -> Term -> Term -> TopLevel
    ||| syntax ... : ...
    Syntax : Range -> Operator -> TopLevel
    ||| let-type x ≔ t
    LetTypeSignature : Range -> VarName -> Term -> TopLevel
    ||| define-type x ≔ t
    DefineTypeSignature : Range -> VarName -> Term -> TopLevel

namespace OpFreeTerm
  public export
  data OpFreeTopLevel : Type where
    ||| assume x : T
    TypingSignature : Range -> VarName -> OpFreeTerm -> OpFreeTopLevel
    ||| let x : T
    |||       ≔ t
    LetSignature : Range -> VarName -> OpFreeTerm -> OpFreeTerm -> OpFreeTopLevel
    ||| define x : T
    |||          ≔ t
    DefineSignature : Range -> VarName -> OpFreeTerm -> OpFreeTerm -> OpFreeTopLevel
    ||| let-type x ≔ t
    LetTypeSignature : Range -> VarName -> OpFreeTerm -> OpFreeTopLevel
    ||| define-type x ≔ t
    DefineTypeSignature : Range -> VarName -> OpFreeTerm -> OpFreeTopLevel

covering
public export
Show TopLevel where
  show (TypingSignature r x ty) =
    "assume \{x} : \{show ty}"
  show (LetSignature r x ty rhs) =
    "let \{x} : \{show ty} ≔ \{show rhs}"
  show (DefineSignature r x ty rhs) =
    "define \{x} : \{show ty} ≔ \{show rhs}"
  show (Syntax r op) =
    "syntax ..."
  show (LetTypeSignature r x rhs) =
    "let-type \{x} ≔ \{show rhs}"
  show (DefineTypeSignature r x rhs) =
    "define-type \{x} ≔ \{show rhs}"

covering
public export
Show OpFreeTopLevel where
  show (TypingSignature r x ty) =
    "assume \{x} : \{show ty}"
  show (LetSignature r x ty rhs) =
    "let \{x} : \{show ty} ≔ \{show rhs}"
  show (DefineSignature r x ty rhs) =
    "define \{x} : \{show ty} ≔ \{show rhs}"
  show (LetTypeSignature r x rhs) =
    "let-type \{x} ≔ \{show rhs}"
  show (DefineTypeSignature r x rhs) =
    "define-type \{x} ≔ \{show rhs}"

namespace OpFreeTerm
  public export
  range : OpFreeTerm -> Range
  range (PiTy x str y z) = x
  range (ImplicitPiTy x str y z) = x
  range (SigmaTy x str y z) = x
  range (PiVal x str y) = x
  range (ImplicitPiVal x str y) = x
  range (ProdTy x y z) = x
  range (FunTy x y z) = x
  range (TyEqTy x y z) = x
  range (ElEqTy x y z w) = x
  range (SigmaVal x y z) = x
  range (App x y xs) = x
  range (Tac r _) = r

{-
||| A predicate on the term-language defining when a term is a valid path.
-- FIX: This definition makes idris type-checker stall. Almost certainly this is about deep patterns.
public export
isValidPath : OpFreeTerm -> Bool
isValidPath (PiTy x str dom (App _ (Underscore _) [])) = isValidPath dom
isValidPath (PiTy x str (App _ (Underscore _) []) cod) = isValidPath cod
isValidPath (PiTy x str _ _) = False
isValidPath (ImplicitPiTy x str (App _ (Underscore _) []) cod) = isValidPath cod
isValidPath (ImplicitPiTy x str dom (App _ (Underscore _) [])) = isValidPath dom
isValidPath (ImplicitPiTy x str dom cod) = False
isValidPath (SigmaTy x str (App _ (Underscore _) []) cod) = isValidPath cod
isValidPath (SigmaTy x str dom (App _ (Underscore _) [])) = isValidPath dom
isValidPath (SigmaTy x str dom cod) = False
isValidPath (PiVal x str f) = isValidPath f
isValidPath (ImplicitPiVal x str f) = isValidPath f
isValidPath (ProdTy x (App _ (Underscore _) []) cod) = isValidPath cod
isValidPath (ProdTy x dom (App _ (Underscore _) [])) = isValidPath dom
isValidPath (ProdTy x dom cod) = False
isValidPath (FunTy x (App _ (Underscore _) []) cod) = isValidPath cod
isValidPath (FunTy x dom (App _ (Underscore _) [])) = isValidPath dom
isValidPath (FunTy x dom cod) = False
isValidPath (EqTy _ a (App _ (Underscore _) []) (App _ (Underscore _) [])) = isValidPath a
isValidPath (EqTy _ (App _ (Underscore _) []) b (App _ (Underscore _) [])) = isValidPath b
isValidPath (EqTy _ (App _ (Underscore _) []) (App _ (Underscore _) []) c) = isValidPath c
isValidPath (EqTy _ a b c) = False
isValidPath (SigmaVal x a (App _ (Underscore _) [])) = isValidPath a
isValidPath (SigmaVal x (App _ (Underscore _) []) b) = isValidPath b
isValidPath (SigmaVal x a b) = False
isValidPath (App _ (Var x str) es) = False
isValidPath (App _ (NatVal0 x) es) = False
isValidPath (App _ (NatVal1 x) [(_, (Arg ([], t)))]) = isValidPath t
isValidPath (App _ (NatVal1 x) es) = False
isValidPath (App _ (NatElim x) [(_, Arg ([], schema)),
                                (_, Arg ([], (App _ (Underscore _) []))),
                                (_, Arg ([], (App _ (Underscore _) []))),
                                (_, Arg ([], (App _ (Underscore _) [])))]) = isValidPath schema
isValidPath (App _ (NatElim x) [(_, Arg ([], (App _ (Underscore _) []))),
                                (_, Arg ([], z)),
                                (_, Arg ([], (App _ (Underscore _) []))),
                                (_, Arg ([], (App _ (Underscore _) [])))]) = isValidPath z
isValidPath (App _ (NatElim x) [(_, Arg ([], (App _ (Underscore _) []))),
                                (_, Arg ([], (App _ (Underscore _) []))),
                                (_, Arg ([], s)),
                                (_, Arg ([], (App _ (Underscore _) [])))]) = isValidPath s
isValidPath (App _ (NatElim x) [(_, Arg ([], (App _ (Underscore _) []))),
                                (_, Arg ([], (App _ (Underscore _) []))),
                                (_, Arg ([], (App _ (Underscore _) []))),
                                (_, Arg ([], t))]) = isValidPath t
isValidPath (App _ (NatElim x) es) = False
isValidPath (App _ (EqElim x) es) = False
isValidPath (App _ (EqVal x) es) = False
isValidPath (App _ (NatTy x) es) = False
isValidPath (App _ (UniverseTy x) es) = False
isValidPath (App _ (Hole x str mstrs) es) = False
isValidPath (App _ (UnnamedHole x mstrs) es) = False
isValidPath (App _ (Unfold x str) es) = False
isValidPath (App _ (PiBeta x) es) = False
isValidPath (App _ (PiEta x) es) = False
isValidPath (App _ (NatBetaZ x) es) = False
isValidPath (App _ (NatBetaS x) es) = False
isValidPath (App _ (PiEq x) es) = False
isValidPath (App _ (Underscore x) es) = False
isValidPath (App _ (Box x) es) = True
isValidPath (App _ (Tm x y) es) = ?ff_28 -}
