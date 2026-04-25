module Nova.Core.Rigidity

import Nova.Control.Monad.Id

import Data.AVL

import Nova.Core.Evaluation
import Nova.Core.Language

mutual
  namespace Typ
    ||| A term head-neutral w.r.t. open-evaluation is rigid if
    ||| there is no (~) that changes its constructor.
    public export
    isRigidNu : Signature -> Omega -> Typ -> EvalM Bool
    isRigidNu sig omega (PiTy str x y) = pure True
    isRigidNu sig omega (ImplicitPiTy str x y) = pure True
    isRigidNu sig omega (SigmaTy str x y) = pure True
    isRigidNu sig omega NatTy = pure True
    isRigidNu sig omega ZeroTy = pure True
    isRigidNu sig omega OneTy = pure True
    isRigidNu sig omega UniverseTy = pure True
    isRigidNu sig omega (El a) = isRigid sig omega a
    isRigidNu sig omega (ContextSubstElim x y) = assert_total $ idris_crash "isRigidNu(ContextSubstElim)"
    isRigidNu sig omega (SignatureSubstElim x y) = assert_total $ idris_crash "isRigidNu(SignatureSubstElim)"
    isRigidNu sig omega (OmegaVarElim x sigma) =
      case (lookup x omega) of
        Just (LetElem {}) => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(1)"
        Just (LetType {}) => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(1')"
        Just (MetaElem _ _ _) => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(1)"
        Just (MetaType _ SolveByUnification) => pure False
        Just (MetaType _ SolveByElaboration) => pure False
        Just (MetaType _ NoSolve) => pure True
        Just _ => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(2)"
        Nothing => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(3)"
    isRigidNu sig omega (TyEqTy x y) = pure True
    isRigidNu sig omega (ElEqTy x y z) = pure True
    isRigidNu sig omega (SignatureVarElim {}) = pure True

    ||| A term is rigid if
    ||| there is no (~) that changes its constructor.
    public export
    isRigid : Signature -> Omega -> Typ -> EvalM Bool
    isRigid sig omega ty = isRigidNu sig omega !(openEval sig omega ty)

  namespace Elem
    ||| A term head-neutral w.r.t. open-evaluation is rigid if
    ||| there is no (~) that changes its constructor.
    public export
    isRigidNu : Signature -> Omega -> Elem -> EvalM Bool
    isRigidNu sig omega (PiTy str x y) = pure True
    isRigidNu sig omega (ImplicitPiTy str x y) = pure True
    isRigidNu sig omega (SigmaTy str x y) = pure True
    isRigidNu sig omega (PiVal str x y z) = pure True
    isRigidNu sig omega (ImplicitPiVal str x y z) = pure True
    isRigidNu sig omega (SigmaVal {}) = pure True
    isRigidNu sig omega (PiElim x str y z w) = pure True
    isRigidNu sig omega (ImplicitPiElim x str y z w) = pure True
    isRigidNu sig omega (SigmaElim1 {}) = pure True
    isRigidNu sig omega (SigmaElim2 {}) = pure True
    isRigidNu sig omega NatVal0 = pure True
    isRigidNu sig omega (NatVal1 x) = pure True
    isRigidNu sig omega NatTy = pure True
    isRigidNu sig omega ZeroTy = pure True
    isRigidNu sig omega OneTy = pure True
    isRigidNu sig omega OneVal = pure True
    isRigidNu sig omega (ZeroElim _ t) = pure True
    isRigidNu sig omega (NatElim str x y str1 str2 z w) = pure True
    isRigidNu sig omega (ContextSubstElim x y) = assert_total $ idris_crash "isRigidNu(ContextSubstElim)"
    isRigidNu sig omega (SignatureSubstElim x y) = assert_total $ idris_crash "isRigidNu(SignatureSubstElim)"
    isRigidNu sig omega (ContextVarElim k) = pure True
    isRigidNu sig omega (SignatureVarElim k sigma) = pure True
    isRigidNu sig omega (OmegaVarElim x sigma) =
      case (lookup x omega) of
        Just (LetElem {}) => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(1)"
        Just (LetType {}) => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(1')"
        Just (MetaElem _ _ SolveByUnification) => pure False
        Just (MetaElem _ _ SolveByElaboration) => pure False
        Just (MetaElem _ _ NoSolve) => pure True
        Just (MetaType _ _) => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(1'')"
        Just _ => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(2)"
        Nothing => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(3)"
    isRigidNu sig omega (TyEqTy x y) = pure True
    isRigidNu sig omega (ElEqTy x y z) = pure True
    isRigidNu sig omega (TyEqVal _) = pure True
    isRigidNu sig omega (ElEqVal _ _) = pure True

    ||| A term is rigid if
    ||| there is no (~) that changes its constructor.
    public export
    isRigid : Signature -> Omega -> Elem -> EvalM Bool
    isRigid sig omega el = isRigidNu sig omega !(openEval sig omega el)

