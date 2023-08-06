module ETT.Core.Conversion

import ETT.Core.Language
import ETT.Core.Monad
import ETT.Core.Substitution

-- Checking equality of terms modulo substitution rules

-- This equality-check procedure is *incomplete*. It can't be, because equality is undecidable.

mutual
  namespace Elem
    public export
    convNu : Elem -> Elem -> M Bool
    convNu (PiTy x0 a0 b0) (PiTy x1 a1 b1) =
      conv a0 a1 `and` conv b0 b1
    convNu (PiVal x0 _ _ f0) (PiVal x1 _ _ f1) =
      conv f0 f1
    convNu (PiElim f0 x0 a0 b0 e0) (PiElim f1 x1 a1 b1 e1) =
      conv f0 f1 `and` conv e0 e1
    convNu NatVal0 NatVal0 = return True
    convNu Universe Universe = return True
    convNu NatTy NatTy = return True
    convNu (NatVal1 t0) (NatVal1 t1) =
      conv t0 t1
    convNu (NatElim x0 schema0 z0 y0 h0 s0 t0) (NatElim x1 schema1 z1 y1 h1 s1 t1) =
      conv schema0 schema1
        `and`
      conv z0 z1
        `and`
      conv s0 s1
        `and`
      conv t0 t1
    convNu (ContextSubstElim {}) b = throw "convNu(ContextSubstElim)"
    convNu (SignatureSubstElim {}) b = throw "convNu(SignatureSubstElim)"
    convNu (ContextVarElim x0) (ContextVarElim x1) =
      return (x0 == x1)
    convNu (SignatureVarElim x0 sigma) (SignatureVarElim x1 tau) =
     return (x0 == x1)
        `and`
      conv sigma tau
    convNu (EqTy a0 b0 ty0) (EqTy a1 b1 ty1) =
      conv a0 a1 `and` conv b0 b1 `and` conv ty0 ty1
    convNu (EqVal {}) (EqVal {}) = return True
    convNu _ _ = return False

    public export
    conv : Elem -> Elem -> M Bool
    conv a b = convNu (runSubst a) (runSubst b)

  namespace ExtSpine
    public export
    conv : Spine -> Spine -> M Bool
    conv [<] [<] = return True
    conv (_ :< _) [<] = throw "conv(_ :< _, [<])"
    conv [<] (_ :< _) = throw "conv([<], _ :< _)"
    conv (ts0 :< t0) (ts1 :< t1) = conv ts0 ts1 `and` conv t0 t1

  namespace SubstContextNF
    public export
    conv : SubstContextNF -> SubstContextNF -> M Bool
    conv Terminal Terminal = return True
    conv Terminal (WkN k) = return True
    conv Terminal (Ext x y) = return True
    conv (WkN k) Terminal = return True
    conv (WkN k) (WkN j) = return (k == j)
    conv (WkN k) (Ext sigma t) = conv (WkN (S k)) sigma `and` conv (ContextVarElim k) t
    conv (Ext x y) Terminal = return True
    conv (Ext sigma t) (WkN k) = conv (WkN (S k)) sigma `and` conv (ContextVarElim k) t
    conv (Ext sigma t) (Ext tau p) = conv sigma tau `and` conv t p

  namespace SubstContext
    public export
    conv : SubstContext -> SubstContext -> M Bool
    conv sigma tau = conv (eval sigma) (eval tau)


-- Ext σ t = Ext σ' t' <=> σ = σ' ^ t = t'
-- Terminal = _ <=> 𝟙
-- Ext σ t = Wk k <=> σ = Wk (S k) ^ t = Var k
-- Wk k = Wk n <=> k = n
