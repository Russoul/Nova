module Nova.Surface.Language

import Data.Location
import Data.List1
import Data.AlternatingList
import Data.AlternatingList1

import Nova.Core.Name
import Nova.Surface.Operator

-- h ::= Z | Refl | x | S | ℕ-elim | J | ℕ | 𝕌 | !x | ?x | Π-β | Π-η | Π⁼ | ℕ-β-Z | ℕ-β-S

-- e{0} = x ↦ e{≥0} | {x} ↦ e{≥0} | (x : e{≥0}) → e{≥0} | {x : e{≥0} → e{≥0}} | (x : {≥0}) ⨯ e{≥0}
-- e{1} = op e{≥2} op ... e{≥2} op | e{≥2} op e{≥2} ... op e{≥3}
-- e{2} = h ē⁺ where |ē⁺| > 0
-- e{3} = h | (e{≥0})

-- e⁺{0} = x̅.̅ e{≥0}
-- e⁺{1} = e{≥3} | (e⁺{≥0}) | .π₁ | .π₂ | {e{≥0}}
-- ē⁺ ::= ␣ e⁺{1} ē⁺ | ·

-- top-level ::= assume x : e{≥0} | let x : e{≥0} ≔ e{≥0}

mutual
  namespace Head
    public export
    data Head : Type where
      Var : Range -> VarName -> Head
      NatVal0 : Range -> Head
      NatVal1 : Range -> Head
      NatElim : Range -> Head
      EqElim : Range -> Head
      EqVal : Range -> Head
      NatTy : Range -> Head
      UniverseTy : Range -> Head
      Hole : Range -> VarName -> Maybe (List VarName) -> Head
      UnnamedHole : Range -> Maybe (List VarName) -> Head
      Unfold : Range -> VarName -> Head
      PiBeta : Range -> Head
      PiEta : Range -> Head
      NatBetaZ : Range -> Head
      NatBetaS : Range -> Head
      PiEq : Range -> Head
      Tm : Range -> Term -> Head

  namespace OpFreeHead
    public export
    data OpFreeHead : Type where
      Var : Range -> VarName -> OpFreeHead
      NatVal0 : Range -> OpFreeHead
      NatVal1 : Range -> OpFreeHead
      NatElim : Range -> OpFreeHead
      EqElim : Range -> OpFreeHead
      EqVal : Range -> OpFreeHead
      NatTy : Range -> OpFreeHead
      UniverseTy : Range -> OpFreeHead
      Hole : Range -> VarName -> Maybe (List VarName) -> OpFreeHead
      UnnamedHole : Range -> Maybe (List VarName) -> OpFreeHead
      Unfold : Range -> VarName -> OpFreeHead
      PiBeta : Range -> OpFreeHead
      PiEta : Range -> OpFreeHead
      NatBetaZ : Range -> OpFreeHead
      NatBetaS : Range -> OpFreeHead
      PiEq : Range -> OpFreeHead
      Tm : Range -> OpFreeTerm -> OpFreeHead

  namespace Term
    public export
    data Term : Type where
      PiTy : Range -> VarName -> Term -> Term -> Term
      ImplicitPiTy : Range -> VarName -> Term -> Term -> Term
      SigmaTy : Range -> VarName -> Term -> Term -> Term
      PiVal : Range -> VarName -> Term -> Term
      ImplicitPiVal : Range -> VarName -> Term -> Term
      OpLayer : {k : _} -> Range -> AlternatingList1 k (Range, String) (Range, Head, Elim) -> Term

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
      EqTy : Range -> OpFreeTerm -> OpFreeTerm -> OpFreeTerm -> OpFreeTerm
      SigmaVal : Range -> OpFreeTerm -> OpFreeTerm -> OpFreeTerm
      App : Range -> OpFreeHead -> OpFreeElim -> OpFreeTerm

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
  Elim = List ElimEntry

  public export
  OpFreeElim : Type
  OpFreeElim = List OpFreeElimEntry

public export
range : Term -> Range
range (PiTy r str y z) = r
range (ImplicitPiTy r str y z) = r
range (SigmaTy r str y z) = r
range (PiVal r str y) = r
range (ImplicitPiVal r str y) = r
range (OpLayer r ls) = r

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
    show (EqElim x) = "J"
    show (EqVal x) = "Refl"
    show (NatTy x) = "ℕ"
    show (UniverseTy x) = "𝕌"
    show (PiEq x) = "PiEq"
    show (Tm x tm) = "Tm(\{show tm})"

  public export
  covering
  Show Term where
    show (PiTy _ x a b) = "PiTy(\{show a}, \{show b})"
    show (SigmaTy _ x a b) = "SigmaTy(\{show a}, \{show b})"
    show (ImplicitPiTy _ x a b) = "ImplicitPiTy(\{show a}, \{show b})"
    show (PiVal _ x f) = "PiVal(\{x}, \{show f})"
    show (ImplicitPiVal _ x f) = "ImplicitPiVal(\{x}, \{show f})"
    show (OpLayer _ list) = "OpLayer(\{show list})"

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
    show (NatElim x) = "ℕ-elim"
    show (EqElim x) = "J"
    show (EqVal x) = "Refl"
    show (NatTy x) = "ℕ"
    show (UniverseTy x) = "𝕌"
    show (PiEq x) = "PiEq"
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
    show (EqTy _ a b ty) = "EqTy(\{show a}, \{show b}, \{show ty})"
    show (SigmaVal _ a b) = "SigmaVal(\{show a}, \{show b})"
    show (App _ head list) = "App(\{show head}, \{show list})"

namespace Term
  public export
  data TopLevel : Type where
    ||| assume x : T
    TypingSignature : Range -> VarName -> Term -> TopLevel
    ||| let x : T
    |||       ≔ t
    LetSignature : Range -> VarName -> Term -> Term -> TopLevel
    ||| syntax ... : ...
    Syntax : Range -> Operator -> TopLevel

namespace OpFreeTerm
  public export
  data OpFreeTopLevel : Type where
    ||| assume x : T
    TypingSignature : Range -> VarName -> OpFreeTerm -> OpFreeTopLevel
    ||| let x : T
    |||       ≔ t
    LetSignature : Range -> VarName -> OpFreeTerm -> OpFreeTerm -> OpFreeTopLevel

covering
public export
Show TopLevel where
  show (TypingSignature r x ty) =
    "assume \{x} : \{show ty}"
  show (LetSignature r x ty rhs) =
    "let \{x} : \{show ty} ≔ \{show rhs}"
  show (Syntax r op) =
    "syntax ..."

covering
public export
Show OpFreeTopLevel where
  show (TypingSignature r x ty) =
    "assume \{x} : \{show ty}"
  show (LetSignature r x ty rhs) =
    "let \{x} : \{show ty} ≔ \{show rhs}"
