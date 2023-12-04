module Nova.Core.Rigidity

import Data.AVL

import Nova.Core.Evaluation
import Nova.Core.Language
import Nova.Core.Monad

mutual
  namespace Typ
    ||| A term head-neutral w.r.t. open-evaluation is rigid if
    ||| there is no (~) that changes its constructor.
    public export
    isRigidNu : Signature -> Omega -> Typ -> M Bool
    isRigidNu sig omega (PiTy str x y) = return True
    isRigidNu sig omega (ImplicitPiTy str x y) = return True
    isRigidNu sig omega (SigmaTy str x y) = return True
    isRigidNu sig omega NatTy = return True
    isRigidNu sig omega ZeroTy = return True
    isRigidNu sig omega OneTy = return True
    isRigidNu sig omega UniverseTy = return True
    isRigidNu sig omega (El a) = isRigid sig omega a
    isRigidNu sig omega (ContextSubstElim x y) = assert_total $ idris_crash "isRigidNu(ContextSubstElim)"
    isRigidNu sig omega (SignatureSubstElim x y) = assert_total $ idris_crash "isRigidNu(SignatureSubstElim)"
    isRigidNu sig omega (OmegaVarElim x sigma) =
      case (lookup x omega) of
        Just (LetElem {}) => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(1)"
        Just (LetType {}) => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(1')"
        Just (MetaElem _ _ _) => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(1)"
        Just (MetaType _ SolveByUnification) => return False
        Just (MetaType _ SolveByElaboration) => return False
        Just (MetaType _ NoSolve) => return True
        Just _ => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(2)"
        Nothing => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(3)"
    isRigidNu sig omega (TyEqTy x y) = return True
    isRigidNu sig omega (ElEqTy x y z) = return True

    ||| A term is rigid if
    ||| there is no (~) that changes its constructor.
    public export
    isRigid : Signature -> Omega -> Typ -> M Bool
    isRigid sig omega ty = isRigidNu sig omega !(openEval sig omega ty)

  namespace Elem
    ||| A term head-neutral w.r.t. open-evaluation is rigid if
    ||| there is no (~) that changes its constructor.
    public export
    isRigidNu : Signature -> Omega -> Elem -> M Bool
    isRigidNu sig omega (PiTy str x y) = return True
    isRigidNu sig omega (ImplicitPiTy str x y) = return True
    isRigidNu sig omega (SigmaTy str x y) = return True
    isRigidNu sig omega (PiVal str x y z) = return True
    isRigidNu sig omega (ImplicitPiVal str x y z) = return True
    isRigidNu sig omega (SigmaVal {}) = return True
    isRigidNu sig omega (PiElim x str y z w) = return True
    isRigidNu sig omega (ImplicitPiElim x str y z w) = return True
    isRigidNu sig omega (SigmaElim1 {}) = return True
    isRigidNu sig omega (SigmaElim2 {}) = return True
    isRigidNu sig omega NatVal0 = return True
    isRigidNu sig omega (NatVal1 x) = return True
    isRigidNu sig omega NatTy = return True
    isRigidNu sig omega ZeroTy = return True
    isRigidNu sig omega OneTy = return True
    isRigidNu sig omega OneVal = return True
    isRigidNu sig omega (ZeroElim t) = return True
    isRigidNu sig omega (NatElim str x y str1 str2 z w) = return True
    isRigidNu sig omega (ContextSubstElim x y) = assert_total $ idris_crash "isRigidNu(ContextSubstElim)"
    isRigidNu sig omega (SignatureSubstElim x y) = assert_total $ idris_crash "isRigidNu(SignatureSubstElim)"
    isRigidNu sig omega (ContextVarElim k) = return True
    isRigidNu sig omega (SignatureVarElim k sigma) = return True
    isRigidNu sig omega (OmegaVarElim x sigma) =
      case (lookup x omega) of
        Just (LetElem {}) => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(1)"
        Just (LetType {}) => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(1')"
        Just (MetaElem _ _ SolveByUnification) => return False
        Just (MetaElem _ _ SolveByElaboration) => return False
        Just (MetaElem _ _ NoSolve) => return True
        Just (MetaType _ _) => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(1'')"
        Just _ => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(2)"
        Nothing => assert_total $ idris_crash "isRigidNu(SignatureVarElim)(3)"
    isRigidNu sig omega (TyEqTy x y) = return True
    isRigidNu sig omega (ElEqTy x y z) = return True
    isRigidNu sig omega TyEqVal = return True
    isRigidNu sig omega ElEqVal = return True

    ||| A term is rigid if
    ||| there is no (~) that changes its constructor.
    public export
    isRigid : Signature -> Omega -> Elem -> M Bool
    isRigid sig omega el = isRigidNu sig omega !(openEval sig omega el)

