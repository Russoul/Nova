module Nova.ComputeTest

-- Standalone test suite for Nova.Compute. Every check constructs a
-- closed core term directly as an Elem/Ty value (no parser involved —
-- Nova.Kernel.Parser has no surface form for a Sig, which several
-- checks below need to build) and compares whnf/nf's output against an
-- expected value via the derived Eq instances, printing a PASS/FAIL
-- line per check and exiting non-zero if any check fails.

import Data.List
import Data.SnocList
import System

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Compute

%default covering

-- ===== A tiny standalone test harness =====

record Check where
  constructor MkCheck
  name     : String
  passed   : Bool
  actual   : String
  expected : String

check : (Eq a, Show a) => String -> a -> a -> Check
check name actual expected =
  MkCheck name (actual == expected) (show actual) (show expected)

emptySig : Sig
emptySig = [<]

-- ===== whnf: the head redex chain, and only the head redex chain =====

whnfChecks : List Check
whnfChecks =
  [ check "whnf: Π-β"
      (whnfElem emptySig (PiApp (PiIntro (CtxVar 0)) OneIntro))
      OneIntro

  , check "whnf: Π-β chases a newly-exposed head (id (id Z) -> Z)"
      (whnfElem emptySig (PiApp (PiIntro (CtxVar 0)) (PiApp (PiIntro (CtxVar 0)) NatIntro0)))
      NatIntro0

  , check "whnf: does NOT recurse under a canonical head (S (redex) stays S (redex))"
      (whnfElem emptySig (NatIntro1 (PiApp (PiIntro (CtxVar 0)) NatIntro0)))
      (NatIntro1 (PiApp (PiIntro (CtxVar 0)) NatIntro0))

  , check "whnf: Σ-β₁"
      (whnfElem emptySig (SigmaElim1 (SigmaIntro OneIntro NatIntro0)))
      OneIntro

  , check "whnf: Σ-β₂"
      (whnfElem emptySig (SigmaElim2 (SigmaIntro OneIntro NatIntro0)))
      NatIntro0

  , check "whnf: Σ-β₁ chases a redex scrutinee"
      (whnfElem emptySig (SigmaElim1 (PiApp (PiIntro (CtxVar 0)) (SigmaIntro OneIntro NatIntro0))))
      OneIntro

  , check "whnf: ℕ-elim-β-Z"
      (whnfElem emptySig (NatElim OneIntro (NatIntro1 (CtxVar 0)) NatIntro0))
      OneIntro

  , check "whnf: ℕ-elim-β-S exposes exactly one layer (doubling 2, one step: S (S (ℕ-elim … 1)))"
      (whnfElem emptySig doubling2)
      (NatIntro1 (NatIntro1 (NatElim NatIntro0 doublingStep one)))

  , check "whnf: quot-elim-β"
      (whnfElem emptySig (QuotElim (CtxVar 0) (Class NatIntro0)))
      NatIntro0

  , check "whnf: quot-elim-β, body uses its representative"
      (whnfElem emptySig (QuotElim (NatIntro1 (CtxVar 0)) (Class NatIntro0)))
      (NatIntro1 NatIntro0)

  , check "whnf: El-𝟘"  (whnfTy emptySig (El Elem.ZeroTy)) Ty.ZeroTy
  , check "whnf: El-𝟙"  (whnfTy emptySig (El Elem.OneTy))  Ty.OneTy
  , check "whnf: El-ℕ"  (whnfTy emptySig (El Elem.NatTy))  Ty.NatTy

  , check "whnf: El-(→) decodes one layer, components left un-decoded"
      (whnfTy emptySig (El (Elem.PiTy Elem.ZeroTy Elem.OneTy)))
      (Ty.PiTy (El Elem.ZeroTy) (El Elem.OneTy))

  , check "whnf: El-(⨯) decodes one layer, components left un-decoded"
      (whnfTy emptySig (El (Elem.SigmaTy Elem.ZeroTy Elem.OneTy)))
      (Ty.SigmaTy (El Elem.ZeroTy) (El Elem.OneTy))

  , check "whnf: El-(≡)"
      (whnfTy emptySig (El (Elem.EqTy NatIntro0 NatIntro0 Elem.NatTy)))
      (EqTy NatIntro0 NatIntro0 (El Elem.NatTy))

  , check "whnf: El-(/) leaves the Ω-valued relation undecoded"
      (whnfTy emptySig (El (QuotTy Elem.ZeroTy Star)))
      (Quotient (El Elem.ZeroTy) Star)

  , check "whnf: El chases a redex code before deciding whether to decode"
      (whnfTy emptySig (El (PiApp (PiIntro (CtxVar 0)) Elem.NatTy)))
      Ty.NatTy
  ]
 where
  one : Elem
  one = NatIntro1 NatIntro0
  two : Elem
  two = NatIntro1 one
  -- s = S (S ☐₀): "double the recursive result", ignoring the predecessor (☐₁)
  doublingStep : Elem
  doublingStep = NatIntro1 (NatIntro1 (CtxVar 0))
  doubling2 : Elem
  doubling2 = NatElim NatIntro0 doublingStep two

-- ===== nf: whnf, then recurse — except under co-data =====

nfChecks : List Check
nfChecks =
  [ check "nf: fully unrolls ℕ-elim across every layer (doubling 2 = 4)"
      (nfElem emptySig doubling2)
      four

  , check "nf: fully unrolls ℕ-elim across every layer (doubling 3 = 6)"
      (nfElem emptySig doubling3)
      six

  , check "nf: Σ-type's first component (no binder crossed) decodes further; its second (under a binder) does not"
      (nfTy emptySig (El (Elem.SigmaTy Elem.ZeroTy Elem.OneTy)))
      (Ty.SigmaTy Ty.ZeroTy (El Elem.OneTy))

  , check "nf: Π is co-data — El-(→) decodes ONE layer only, then stops (the note's key consequence)"
      (nfTy emptySig (El (Elem.PiTy Elem.ZeroTy Elem.OneTy)))
      (Ty.PiTy (El Elem.ZeroTy) (El Elem.OneTy))

  , check "nf: a λ's body is co-data — left exactly as whnf produced it, redex and all"
      (nfElem emptySig (PiIntro (PiApp (PiIntro (CtxVar 0)) NatIntro0)))
      (PiIntro (PiApp (PiIntro (CtxVar 0)) NatIntro0))

  , check "nf: a pair's components ARE recursed into (Σ is data)"
      (nfElem emptySig (SigmaIntro (PiApp (PiIntro (CtxVar 0)) OneIntro) (SigmaElim1 (SigmaIntro NatIntro0 OneIntro))))
      (SigmaIntro OneIntro NatIntro0)

  , check "nf: a quotient's carrier (no binder crossed) is decoded further; its relation (under a binder) is left exactly as whnf produced it, redex and all"
      (nfTy emptySig (Quotient (El (Elem.SigmaTy Elem.ZeroTy Elem.OneTy)) (PiApp (PiIntro (CtxVar 0)) Star)))
      (Quotient (Ty.SigmaTy Ty.ZeroTy (El Elem.OneTy)) (PiApp (PiIntro (CtxVar 0)) Star))

  , check "nf: quot-elim, fully settled"
      (nfElem emptySig (QuotElim (NatIntro1 (CtxVar 0)) (Class (PiApp (PiIntro (CtxVar 0)) NatIntro0))))
      (NatIntro1 NatIntro0)
  ]
 where
  one : Elem
  one = NatIntro1 NatIntro0
  two : Elem
  two = NatIntro1 one
  three : Elem
  three = NatIntro1 two
  four : Elem
  four = NatIntro1 (NatIntro1 (NatIntro1 (NatIntro1 NatIntro0)))
  six : Elem
  six = NatIntro1 (NatIntro1 (NatIntro1 (NatIntro1 (NatIntro1 (NatIntro1 NatIntro0)))))
  doublingStep : Elem
  doublingStep = NatIntro1 (NatIntro1 (CtxVar 0))
  doubling2 : Elem
  doubling2 = NatElim NatIntro0 doublingStep two
  doubling3 : Elem
  doubling3 = NatElim NatIntro0 doublingStep three

-- ===== x[e˲]: signature-variable unfolding (el-sig-beta / ty-sig-beta) =====
--
-- No surface form for a Sig exists in Nova.Kernel.Parser, so these are
-- built directly.

-- unit ≔ () : 𝟙  (Γ = ε)
sigUnit : Sig
sigUnit = [<] :< SigDef [<] "unit" OneIntro Ty.OneTy

-- MyOne ≔ 𝟙 type  (Γ = ε)
sigMyOne : Sig
sigMyOne = [<] :< SigTyDef [<] "MyOne" Ty.OneTy

-- double ≔ λn. ℕ-elim Z (S (S ☐₀)) n : ℕ → ℕ  (Γ = ε)
sigDouble : Sig
sigDouble =
  [<] :< SigDef [<] "double"
        (PiIntro (NatElim NatIntro0 (NatIntro1 (NatIntro1 (CtxVar 0))) (CtxVar 0)))
        (Ty.PiTy Ty.NatTy Ty.NatTy)

-- redex ≔ (λn. S n) (S Z) : ℕ  — a definiens that is ITSELF a redex
sigRedex : Sig
sigRedex =
  [<] :< SigDef [<] "redex"
        (PiApp (PiIntro (NatIntro1 (CtxVar 0))) (NatIntro1 NatIntro0))
        Ty.NatTy

sigVarChecks : List Check
sigVarChecks =
  [ check "whnf: x[e˲] unfolds a term definition (el-sig-beta)"
      (whnfElem sigUnit (SigVar "unit" [<]))
      OneIntro

  , check "whnf: x[e˲] unfolds a type definition (ty-sig-beta)"
      (whnfTy sigMyOne (Ty.SigVar "MyOne" [<]))
      Ty.OneTy

  , check "whnf: x[e˲] unfolding continues reducing the unfolded body"
      (whnfElem sigRedex (SigVar "redex" [<]))
      (NatIntro1 (NatIntro1 NatIntro0))

  , check "whnf: applying a signature-defined function unfolds through the call (double 2 = 4, one whnf step exposes S (S …))"
      (whnfElem sigDouble (PiApp (SigVar "double" [<]) (NatIntro1 (NatIntro1 NatIntro0))))
      (NatIntro1 (NatIntro1 (NatElim NatIntro0 (NatIntro1 (NatIntro1 (CtxVar 0))) (NatIntro1 NatIntro0))))

  , check "nf: applying a signature-defined function, fully settled (double 2 = 4)"
      (nfElem sigDouble (PiApp (SigVar "double" [<]) (NatIntro1 (NatIntro1 NatIntro0))))
      (NatIntro1 (NatIntro1 (NatIntro1 (NatIntro1 NatIntro0))))
  ]

allChecks : List Check
allChecks = whnfChecks ++ nfChecks ++ sigVarChecks

main : IO ()
main = do
  traverse_ report allChecks
  let failed = filter (not . passed) allChecks
  if isNil failed
    then putStrLn "\{show (length allChecks)}/\{show (length allChecks)} Nova.Compute tests passed."
    else do
      putStrLn "\{show (length failed)}/\{show (length allChecks)} Nova.Compute tests FAILED:"
      traverse_ (\c => putStrLn "  - \{c.name}\n      actual:   \{c.actual}\n      expected: \{c.expected}") failed
      exitFailure
 where
  report : Check -> IO ()
  report c = putStrLn ((if c.passed then "[PASS] " else "[FAIL] ") ++ c.name)
