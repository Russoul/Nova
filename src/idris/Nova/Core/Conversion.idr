module Nova.Core.Conversion

import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Substitution
import Nova.Core.Evaluation

-- Checking equality of terms modulo substitution rules

-- This equality-check procedure is *incomplete*. It can't be, because equality is undecidable.

mutual
  namespace Typ
    public export
    convNu : Signature -> Omega -> Typ -> Typ -> M Bool
    convNu sig omega (PiTy x0 a0 b0) (PiTy x1 a1 b1) =
      conv sig omega a0 a1 `and` conv sig omega b0 b1
    convNu sig omega (ImplicitPiTy x0 a0 b0) (ImplicitPiTy x1 a1 b1) =
      conv sig omega a0 a1 `and` conv sig omega b0 b1
    convNu sig omega (SigmaTy x0 a0 b0) (SigmaTy x1 a1 b1) =
      conv sig omega a0 a1 `and` conv sig omega b0 b1
    convNu sig omega NatTy NatTy = return True
    convNu sig omega ZeroTy ZeroTy = return True
    convNu sig omega OneTy OneTy = return True
    convNu sig omega UniverseTy UniverseTy = return True
    convNu sig omega (El a0) (El a1) = conv sig omega a0 a1
    convNu sig omega (ContextSubstElim {}) b = criticalError "convNu(ContextSubstElim)"
    convNu sig omega (SignatureSubstElim {}) b = criticalError "convNu(SignatureSubstElim)"
    convNu sig omega (OmegaVarElim x0 sigma) (OmegaVarElim x1 tau) =
     return (x0 == x1)
        `and`
      conv sig omega sigma tau
    convNu sig omega (TyEqTy a0 b0) (TyEqTy a1 b1) =
      conv sig omega a0 a1 `and` conv sig omega b0 b1
    convNu sig omega (ElEqTy a0 b0 ty0) (ElEqTy a1 b1 ty1) =
      conv sig omega a0 a1 `and` conv sig omega b0 b1 `and` conv sig omega ty0 ty1
    convNu sig omega (SignatureVarElim x0 sigma) (SignatureVarElim x1 tau) =
     return (x0 == x1)
        `and`
      conv sig omega sigma tau
    convNu _ _ _ _ = return False

    public export
    conv : Signature -> Omega -> Typ -> Typ -> M Bool
    conv sig omega a b = convNu sig omega !(openEval sig omega a) !(openEval sig omega b)

  namespace Elem
    public export
    convNu : Signature -> Omega -> Elem -> Elem -> M Bool
    convNu sig omega (PiTy x0 a0 b0) (PiTy x1 a1 b1) =
      conv sig omega a0 a1 `and` conv sig omega b0 b1
    convNu sig omega (ImplicitPiTy x0 a0 b0) (ImplicitPiTy x1 a1 b1) =
      conv sig omega a0 a1 `and` conv sig omega b0 b1
    convNu sig omega (SigmaTy x0 a0 b0) (SigmaTy x1 a1 b1) =
      conv sig omega a0 a1 `and` conv sig omega b0 b1
    convNu sig omega (PiVal x0 _ _ f0) (PiVal x1 _ _ f1) =
      conv sig omega f0 f1
    convNu sig omega (ImplicitPiVal x0 _ _ f0) (ImplicitPiVal x1 _ _ f1) =
      conv sig omega f0 f1
    convNu sig omega (SigmaVal _ _ _ p0 q0) (SigmaVal _ _ _ p1 q1) =
      conv sig omega p0 p1 `and` conv sig omega q0 q1
    convNu sig omega (PiElim f0 x0 a0 b0 e0) (PiElim f1 x1 a1 b1 e1) =
      conv sig omega f0 f1 `and` conv sig omega e0 e1
    convNu sig omega (ImplicitPiElim f0 x0 a0 b0 e0) (ImplicitPiElim f1 x1 a1 b1 e1) =
      conv sig omega f0 f1 `and` conv sig omega e0 e1
    convNu sig omega (SigmaElim1 f0 x0 a0 b0) (SigmaElim1 f1 x1 a1 b1) =
      conv sig omega f0 f1
    convNu sig omega (SigmaElim2 f0 x0 a0 b0) (SigmaElim2 f1 x1 a1 b1) =
      conv sig omega f0 f1
    convNu sig omega NatVal0 NatVal0 = return True
    convNu sig omega NatTy NatTy = return True
    convNu sig omega ZeroTy ZeroTy = return True
    convNu sig omega OneTy OneTy = return True
    convNu sig omega OneVal OneVal = return True
    convNu sig omega (NatVal1 t0) (NatVal1 t1) =
      conv sig omega t0 t1
    convNu sig omega (NatElim x0 schema0 z0 y0 h0 s0 t0) (NatElim x1 schema1 z1 y1 h1 s1 t1) =
      conv sig omega t0 t1
        `and`
      conv sig omega schema0 schema1
        `and`
      conv sig omega z0 z1
        `and`
      conv sig omega s0 s1
    convNu sig omega (ZeroElim _ t0) (ZeroElim _ t1) =
      conv sig omega t0 t1
    convNu sig omega (ContextSubstElim {}) b = criticalError "convNu(ContextSubstElim)"
    convNu sig omega (SignatureSubstElim {}) b = criticalError "convNu(SignatureSubstElim)"
    convNu sig omega (ContextVarElim x0) (ContextVarElim x1) =
      return (x0 == x1)
    convNu sig omega (SignatureVarElim x0 sigma) (SignatureVarElim x1 tau) =
     return (x0 == x1)
        `and`
      conv sig omega sigma tau
    convNu sig omega (OmegaVarElim x0 sigma) (OmegaVarElim x1 tau) =
     return (x0 == x1)
        `and`
      conv sig omega sigma tau
    convNu sig omega (TyEqTy a0 b0) (TyEqTy a1 b1) =
      conv sig omega a0 a1 `and` conv sig omega b0 b1
    convNu sig omega (ElEqTy a0 b0 ty0) (ElEqTy a1 b1 ty1) =
      conv sig omega a0 a1 `and` conv sig omega b0 b1 `and` conv sig omega ty0 ty1
    convNu sig omega (TyEqVal {}) (TyEqVal {}) = return True
    convNu sig omega (ElEqVal {}) (ElEqVal {}) = return True
    convNu _ _ _ _ = return False

    public export
    conv : Signature -> Omega -> Elem -> Elem -> M Bool
    conv sig omega a b = convNu sig omega !(openEval sig omega a) !(openEval sig omega b)

  namespace ExtSpine
    public export
    conv : Signature -> Omega -> Spine -> Spine -> M Bool
    conv sig omega [<] [<] = return True
    conv sig omega (_ :< _) [<] = criticalError "conv(_ :< _, [<])"
    conv sig omega [<] (_ :< _) = criticalError "conv([<], _ :< _)"
    conv sig omega (ts0 :< t0) (ts1 :< t1) = conv sig omega ts0 ts1 `and` conv sig omega t0 t1

  namespace SubstContextNF
    public export
    conv : Signature -> Omega -> SubstContextNF -> SubstContextNF -> M Bool
    conv sig omega Terminal Terminal = return True
    conv sig omega Terminal (WkN k) = return True
    conv sig omega Terminal (Ext x y) = return True
    conv sig omega (WkN k) Terminal = return True
    conv sig omega (WkN k) (WkN j) = return (k == j)
    conv sig omega (WkN k) (Ext sigma t) = conv sig omega (WkN (S k)) sigma `and` conv sig omega (ContextVarElim k) t
    conv sig omega (Ext x y) Terminal = return True
    conv sig omega (Ext sigma t) (WkN k) = conv sig omega (WkN (S k)) sigma `and` conv sig omega (ContextVarElim k) t
    conv sig omega (Ext sigma t) (Ext tau p) = conv sig omega sigma tau `and` conv sig omega t p

  namespace SubstContext
    public export
    conv : Signature -> Omega -> SubstContext -> SubstContext -> M Bool
    conv sig omega sigma tau = conv sig omega (eval sigma) (eval tau)


-- Ext σ t = Ext σ' t' <=> σ = σ' ^ t = t'
-- Terminal = _ <=> 𝟙
-- Ext σ t = Wk k <=> σ = Wk (S k) ^ t = Var k
-- Wk k = Wk n <=> k = n
