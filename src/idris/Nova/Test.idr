module Nova.Test

import System
import System.File
import Data.List
import Data.SnocList
import Test.Golden

import Me.Russoul.Text.Range

import Nova.Kernel.Syntax
import Nova.Kernel.Parser
import Nova.Kernel
import Nova.Kernel.Derivation
import Nova.Elaboration.Named
import Nova.Elaboration
import Nova.Elaboration.Loader
import Nova.Elaboration.Surface
import Nova.Elaboration.Parser

import Nova.LSP.TestClient

-- ===== Parser mode =====
-- Invoked as: nova-foundation-tests run PARSER INPUT

runParse : String -> String -> IO ()
runParse parser input =
  case parser of
    "sub"          => putStrLn $ either (const "ERROR") show (runParser parseSub input)
    "ty"           => putStrLn $ either (const "ERROR") show (runParser parseTy input)
    "elem"         => putStrLn $ either (const "ERROR") show (runParser parseElem input)
    "surface-ty"   => putStrLn $ either (const "ERROR") (show . snd) (runSurfaceParser (parseSTy [] [<]) input)
    "surface-elem" => putStrLn $ either (const "ERROR") (show . snd) (runSurfaceParser (parseSElem [] [<]) input)
    "surface-item" => putStrLn $ either (const "ERROR") (show . snd) (runSurfaceParser (parseSItem []) input)
    _              => putStrLn "ERROR: unknown parser '\{parser}'"

-- ===== Test suite mode =====
-- Invoked as: nova-foundation-tests PATH_TO_SELF [golden-options...]

-- ===== Derivation-checker mode =====
-- Hard-coded candidate derivations for the phase-1 trusted core
-- (docs/NovaDerivations.txt); each prints its name and the computed
-- conclusion or the rejection reason.

derivCases : List (String, Deriv)
derivCases =
  [ ("id-fun", DElPiI DTyNat (DElVar 0))
  , ("pred", DElPiI DTyNat
      (DElNatE DTyNat DElNatZ (DElVar 1) (DElVar 0)))
  , ("beta-oracle", DNfEq
      (DElPiE (DElPiI DTyNat (DElVar 0)) DElNatZ DTyNat)
      DElNatZ)
  , ("reflect-roundtrip", DElReflect (DElEqI (DElRefl DElNatZ)))
  , ("presup-left", DPresupElL (DNfEq
      (DElPiE (DElPiI DTyNat (DElVar 0)) DElNatZ DTyNat)
      DElNatZ))
  , ("eta-pi", DElPiEta (DElPiI DTyNat (DElVar 0)))
    -- REJECTIONS: a garbage domain dies at its formation premise …
  , ("garbage-domain", DElPiI (DTyEl DElNatZ) (DElVar 0))
    -- … and a transitivity whose middles differ dies at the side
    -- condition
  , ("trans-mismatch", DElTrans (DElRefl DElNatZ)
      (DElRefl (DElNatS DElNatZ)))
    -- an untyped oracle claim is unrepresentable: the premise slot
    -- demands a typing derivation, so an equation between elements
    -- of DIFFERENT types dies at the type side condition
  , ("oracle-type-clash", DNfEq DElNatZ DElOneI)
    -- quotients: Z and S Z are equal classes under the total relation
  , ("quot-class-eq", DElQuotEq DElNatZ (DElNatS DElNatZ)
      (DCodeSquash DTyOne) (DElSquashI DElOneI))
    -- el-nat-eta, replayable at last: the identity candidate twice
  , ("nat-eta", DElNatEta DTyNat (DElVar 0) (DElVar 0)
      DElNatZ (DElNatS (DElVar 1))
      (DElRefl DElNatZ)
      (DElRefl (DElNatS (DElVar 0)))
      (DElRefl (DElNatS (DElVar 0)))
      (DElNatS DElNatZ))
    -- the ν layer: formation at K ℕ ⨯ 𝕏
  , ("nu-type", DTyNu (DPolyK (PProd (PConst Elem.NatTy) PHole) [DCodeNat]))
    -- el-sub-cong-fix: a reflexive equation over ▷ℕ, instantiated
  , ("sub-cong-fix", DElSubCongFix
      (DSubExt DSubId DTyNat DElNatZ)
      (DElRefl (DElVar 0)))
    -- REJECTION: a quotient witness at the wrong proposition
  , ("quot-bad-witness", DElQuotEq DElNatZ (DElNatS DElNatZ)
      (DCodeSquash DTyOne) (DElEqI (DElRefl DElNatZ)))
  ]

runDerivTests : IO ()
runDerivTests =
  for_ derivCases $ \(name, d) =>
    case concludeItem [<] 1000 d of
      Right j => putStrLn "\{name}: \{show j}"
      Left e => putStrLn "\{name}: REJECTED [\{e}]"

pools : IO (List TestPool)
pools = sequence
  [ testsInDir "tests/nova/parser" "Nova Parser"
  , testsInDir "tests/nova/derivation" "Nova Derivation"
  , testsInDir "tests/nova/elaboration" "Nova Elaboration"
  , testsInDir "tests/nova/evaluation" "Nova Evaluation"
  , testsInDir "tests/nova-lsp" "Nova LSP"
  ]

main : IO ()
main = do
  args <- getArgs
  case args of
    (_ :: "run" :: parser :: input :: []) => runParse parser input
    (_ :: "deriv" :: []) => runDerivTests
    (_ :: "elab" :: file :: []) => do
      output <- elabPath file
      putStrLn output
    -- Nova.Application's `run` command, under a different keyword here
    -- since "run" already names the parser-debugging mode above.
    (_ :: "eval" :: file :: name :: []) => do
      result <- runPath file name
      case result of
        Left err  => putStrLn "Error: \{err}"
        Right val => putStrLn val
    (_ :: "lsp" :: lspBin :: fixture :: word :: []) => runLspTest lspBin fixture word
    _ => do
      ps <- pools
      runner ps
