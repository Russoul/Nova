module Nova.Core.Util

import Data.List1

import Nova.Core.Language

public export
funTy : Typ -> Typ -> Typ
funTy a b = PiTy "_" a (ContextSubstElim b Wk)

public export
funTyN1 : List1 Typ -> Typ
funTyN1 (t ::: []) = t
funTyN1 (t ::: o :: os) = funTy t (funTyN1 (o ::: os))

public export
prodTy : Typ -> Typ -> Typ
prodTy a b = SigmaTy "_" a (ContextSubstElim b Wk)
