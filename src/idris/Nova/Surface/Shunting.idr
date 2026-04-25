module Nova.Surface.Shunting

import Me.Russoul.Data.Location

import Nova.Control.Monad.Id

import Data.List1
import Data.SnocList
import Data.Interpolation

import Data.AlternatingList
import Data.AlternatingList1
import Data.AlternatingSnocList
import Data.AlternatingSnocList1

import Nova.Core.Name

import Nova.Surface.Language
import Nova.Surface.Operator

||| Match the given alternating list *layer* against the *op*, generating all possible splits of *layer* by *op*.
||| Initial value of *before* is empty.
||| Example1:
||| op = '+'
||| layer = 'a + b * d + c * d + q'
||| result = [('a', 'b * d + c * d + q'), ('a + b * d', 'c * d + q'), ('a + b * d + c * d', 'q')]
||| Example2:
||| op = '+'
||| layer = 'a + b * d +'
||| result = [('a', 'b * d +'), ('a + b * d', '')]
public export
matchN : (before : AlternatingSnocList (not k) (Range, String) (Range, Head, Elim))
      -> (op : String)
      -> (layer : AlternatingList k (Range, String) (Range, Head, Elim))
      -> List ((k ** AlternatingList k (Range, String) (Range, Head, Elim))
               ,
               (k ** AlternatingList k (Range, String) (Range, Head, Elim))
              )
matchN before op [] = []
matchN before op (ConsA (r, op') rest) =
  case op == op' of
    True => (toList before, (_ ** rest)) :: matchN (SnocA before (r, op')) op rest
    False => matchN (SnocA before (r, op')) op rest
matchN before op (ConsB app rest) = matchN (SnocB before app) op rest

||| Match an n-ry operator *todoOp* against an alternating list *layer*,
||| generating all possible splits of *layer* by *todoOp*.
public export
match :  {k0, k1 : _}
      -> (todoOp : AlternatingList k0 String Nat)
      -> (layer : AlternatingList k1 (Range, String) (Range, Head, Elim))
      -> List (List (Nat, (k ** AlternatingList k (Range, String) (Range, Head, Elim))))
match (ConsA op rest) (ConsA (_, op') rest') =
  case op == op' of
    True => match rest rest'
    False => []
match (ConsA op rest) _ = []
match (ConsB app []) layer = [[(app, (_ ** layer))]]
match (ConsB app (ConsA op rest)) layer = Prelude.do
  (head, tail) <- matchN [<] op layer
  xs <- match rest (snd tail)
  pure ((app, head) :: xs)
match [] [] = [[]]
match [] _ = []

getRange : AlternatingList1 k1 (Range, String) (Range, Head, Elim) -> Range
getRange (ConsA (r, x) []) = r
getRange (ConsB (r, x) []) = r
getRange (ConsA (r, x) (ConsB y zs)) = r + getRange (ConsB y zs)
getRange (ConsB (r, x) (ConsA y zs)) = r + getRange (ConsA y zs)

||| Preprocess builtin operators: we want to map specific applications to
||| builtin operators.
processApp : Range -> String -> List OpFreeTerm -> OpFreeTerm
processApp r "_≡_type" [a, b] = TyEqTy r a b
processApp r "_≡_∈_" [a, b, ty] = ElEqTy r a b ty
processApp r "_⨯_" [a, b] = ProdTy r a b
processApp r "_,_" [a, b] = SigmaVal r a b
processApp r "_→_" [a, b] = FunTy r a b
processApp r op list = App r (Var r op) (map (\t => (range t, Arg ([], t))) list)

mutual
  ||| Try shunting the *layer* via the given operator at specified *lvl* by generating all possible
  ||| splits of *layer* by the given operator and making sure that exactly one split gets through.
  public export
  tryOp : {k1 : _}
       -> List Operator
       -> Operator
       -> Range
       -> (layer : AlternatingList k1 (Range, String) (Range, Head, Elim))
       -> Nat
       -> Either String OpFreeTerm
  tryOp ops op@(MkOperator k seq oplvl) range layer lvl =
    case oplvl >= lvl of
      False => Left "\{toName op}'s level is \{show oplvl} but the target lvl is ≥\{show lvl}"
      True => Id.do
        r <- Id.List.for (match (forget seq) layer) $ \list => Id.do
          Id.List.for list $ \(n, layer) =>
            case layer of
              (_ ** []) => Id.do
                Id.pure (Left "Nothing to parse at target level \{show n}")
              (_ ** ConsA x smth) => shunt ops (OpLayer (getRange (ConsA x smth)) (ConsA x smth)) n
              (_ ** ConsB x smth) => shunt ops (OpLayer (getRange (ConsB x smth)) (ConsB x smth)) n
        let r = map sequence r
        let Right r = exactlyOne r
             | Left err => Left err
        -- write "\{show r}"
        Right $ processApp range (toName op) r
   where
    none : List (Either String a) -> Bool
    none [] = True
    none (Left err :: rest) = none rest
    none (Right x :: rest) = False

    exactlyOne : List (Either String a) -> Either String a
    exactlyOne [] = Left "No alternatives work"
    exactlyOne (Right x :: rest) =
      case none rest of
        True => Right x
        False => Left "Multiple alternatives pass through"
    exactlyOne (Left err :: rest) = exactlyOne rest

  public export
  shuntElimEntry : List Operator -> ElimEntry -> Either String OpFreeElimEntry
  shuntElimEntry ops (Arg (xs, t)) = Prelude.do
    pure (Arg (xs, !(shunt ops t 0)))
  shuntElimEntry ops Pi1 = Prelude.do
    pure Pi1
  shuntElimEntry ops Pi2 = Prelude.do
    pure Pi2
  shuntElimEntry ops (ImplicitArg t) = Prelude.do
    pure (ImplicitArg !(shunt ops t 0))

  public export
  shuntElim : List Operator -> Elim -> Either String OpFreeElim
  shuntElim ops [] = Prelude.do
    pure []
  shuntElim ops ((r, e) :: es) = Prelude.do
    e <- shuntElimEntry ops e
    es <- shuntElim ops es
    pure ((r, e) :: es)

  public export
  shuntHead : List Operator -> Head -> Either String OpFreeHead
  shuntHead ops (Var x str) = Prelude.pure (Var x str)
  shuntHead ops (NatVal0 x) = Prelude.pure (NatVal0 x)
  shuntHead ops (NatVal1 x) = Prelude.pure (NatVal1 x)
  shuntHead ops (OneVal x) = Prelude.pure (OneVal x)
  shuntHead ops (NatElim x) = Prelude.pure (NatElim x)
  shuntHead ops (ZeroElim x) = Prelude.pure (ZeroElim x)
  shuntHead ops (EqElim x) = Prelude.pure (EqElim x)
  shuntHead ops (EqVal x) = Prelude.pure (EqVal x)
  shuntHead ops (NatTy x) = Prelude.pure (NatTy x)
  shuntHead ops (ZeroTy x) = Prelude.pure (ZeroTy x)
  shuntHead ops (OneTy x) = Prelude.pure (OneTy x)
  shuntHead ops (UniverseTy x) = Prelude.pure (UniverseTy x)
  shuntHead ops (Hole x str mstrs) = Prelude.pure (Hole x str mstrs)
  shuntHead ops (UnnamedHole x mstrs) = Prelude.pure (UnnamedHole x mstrs)
  shuntHead ops (Unfold x str) = Prelude.pure (Unfold x str)
  shuntHead ops (PiBeta x) = Prelude.pure (PiBeta x)
  shuntHead ops (PiEta x) = Prelude.pure (PiEta x)
  shuntHead ops (PiEq x) = Prelude.pure (PiEq x)
  shuntHead ops (SigmaBeta1 x) = Prelude.pure (SigmaBeta1 x)
  shuntHead ops (SigmaBeta2 x) = Prelude.pure (SigmaBeta2 x)
  shuntHead ops (SigmaEta x) = Prelude.pure (SigmaEta x)
  shuntHead ops (SigmaEq x) = Prelude.pure (SigmaEq x)
  shuntHead ops (NatBetaZ x) = Prelude.pure (NatBetaZ x)
  shuntHead ops (NatBetaS x) = Prelude.pure (NatBetaS x)
  shuntHead ops (OneEq x) = Prelude.pure (OneEq x)
  shuntHead ops (El x) = Prelude.pure (El x)
  shuntHead ops (Underscore x) = Prelude.pure (Underscore x)
  shuntHead ops (Box x) = Prelude.pure (Box x)
  shuntHead ops (Tm r tm) = Prelude.do
    Prelude.pure (Tm r !(shunt ops tm 0))

  public export
  shuntCtxPath : List Operator -> CtxPath -> Either String OpFreeCtxPath
  shuntCtxPath ops (MkCtxPath range here skipped) =
    Prelude.[| MkOpFreeCtxPath (pure range) (shunt ops here 0) (pure skipped) |]

  public export
  shuntTactic : List Operator -> Tactic -> Either String OpFreeTactic
  shuntTactic ops (Id x) = Prelude.pure (Id x)
  shuntTactic ops (Trivial x) = Prelude.pure (Trivial x)
  shuntTactic ops (Composition r alphas) = Prelude.do
    alphas <- for alphas (shuntTactic ops)
    Prelude.pure (Composition r alphas)
  shuntTactic ops (Unfold r tm) = Prelude.do
    tm <- shunt ops tm 0
    Prelude.pure (Unfold r tm)
  shuntTactic ops (UnfoldCtx r tm) = Prelude.do
    tm <- shuntCtxPath ops tm
    Prelude.pure (UnfoldCtx r tm)
  shuntTactic ops (Exact r tm) = Prelude.do
    tm <- shunt ops tm 0
    Prelude.pure (Exact r tm)
  shuntTactic ops (Split r alphas beta) = Prelude.do
    alphas <- for alphas (shuntTactic ops)
    beta <- shuntTactic ops beta
    Prelude.pure (Split r alphas beta)
  shuntTactic ops (RewriteInv r a b) = Prelude.do
    a <- shunt ops a 3
    b <- shunt ops b 3
    Prelude.pure (RewriteInv r a b)
  shuntTactic ops (Rewrite r a b) = Prelude.do
    a <- shunt ops a 3
    b <- shunt ops b 3
    Prelude.pure (Rewrite r a b)
  shuntTactic ops (Let r x e) = Prelude.do
    e <- shunt ops e 0
    Prelude.pure (Let r x e)
  shuntTactic ops (NormaliseCommutativeMonoid r a o b) = Prelude.do
    a <- shunt ops a 3
    b <- shunt ops b 3
    Prelude.pure (NormaliseCommutativeMonoid r a o b)

  ||| Shunt the given term at the specified *lvl*.
  public export
  shunt : List Operator -> Term -> (lvl : Nat) -> Either String OpFreeTerm
  shunt ops (PiTy r (x ::: []) dom cod) lvl = Prelude.do
    case (lvl > 0) of
      True => Left "Can't parse (_ : _) → _ at level \{show lvl}"
      False => Prelude.do
       dom <- shunt ops dom 0
       cod <- shunt ops cod 0
       pure (PiTy r x dom cod)
  shunt ops (PiTy r (x ::: y :: zs) dom cod) lvl = Prelude.do
    case (lvl > 0) of
      True => Left "Can't parse (_ : _) → _ at level \{show lvl}"
      False => Prelude.do
       dom' <- shunt ops dom 0
       cod' <- shunt ops (PiTy r (y ::: zs) dom cod) 0
       pure (PiTy r x dom' cod')
  shunt ops (ImplicitPiTy r (x ::: []) dom cod) lvl = Prelude.do
    case (lvl > 0) of
      True => Left "Can't parse {_ : _} → _ at level \{show lvl}"
      False => Prelude.do
        dom <- shunt ops dom 0
        cod <- shunt ops cod 0
        pure (ImplicitPiTy r x dom cod)
  shunt ops (ImplicitPiTy r (x ::: y :: zs) dom cod) lvl = Prelude.do
    case (lvl > 0) of
      True => Left "Can't parse {_ : _} → _ at level \{show lvl}"
      False => Prelude.do
        dom' <- shunt ops dom 0
        cod' <- shunt ops (ImplicitPiTy r (y ::: zs) dom cod) 0
        pure (ImplicitPiTy r x dom' cod')
  shunt ops (SigmaTy r (x ::: []) dom cod) lvl = Prelude.do
    case (lvl > 0) of
      True => Left "Can't parse (_ : _) ⨯ _ at level \{show lvl}"
      False => Prelude.do
       dom <- shunt ops dom 0
       cod <- shunt ops cod 0
       pure (SigmaTy r x dom cod)
  shunt ops (SigmaTy r (x ::: y :: zs) dom cod) lvl = Prelude.do
    case (lvl > 0) of
      True => Left "Can't parse (_ : _) ⨯ _ at level \{show lvl}"
      False => Prelude.do
       dom' <- shunt ops dom 0
       cod' <- shunt ops (SigmaTy r (y ::: zs) dom cod) 0
       pure (SigmaTy r x dom' cod')
  shunt ops (PiVal r (x ::: []) f) lvl = Prelude.do
    case (lvl > 0) of
      True => Left "Can't parse _ ↦ _ at level \{show lvl}"
      False => Prelude.do
       f <- shunt ops f 0
       pure (PiVal r x f)
  shunt ops (PiVal r (x ::: y :: zs) f) lvl = Prelude.do
    case (lvl > 0) of
      True => Left "Can't parse _ ↦ _ at level \{show lvl}"
      False => Prelude.do
       f' <- shunt ops (PiVal r (y ::: zs) f) 0
       pure (PiVal r x f')
  shunt ops (ImplicitPiVal r (x ::: []) f) lvl = Prelude.do
    case (lvl > 0) of
      True => Left "Can't parse {_} ↦ _ at level \{show lvl}"
      False => Prelude.do
       f <- shunt ops f 0
       pure (ImplicitPiVal r x f)
  shunt ops (ImplicitPiVal r (x ::: y :: zs) f) lvl = Prelude.do
    case (lvl > 0) of
      True => Left "Can't parse {_} ↦ _ at level \{show lvl}"
      False => Prelude.do
       f' <- shunt ops (ImplicitPiVal r (y ::: zs) f) 0
       pure (ImplicitPiVal r x f')
  shunt ops (Tac r alpha) lvl = Prelude.do
    case (lvl > 0) of
      True => Left "Can't parse tac ... at level \{show lvl}"
      False => Prelude.do
        alpha <- shuntTactic ops alpha
        pure (Tac r alpha)
  shunt ops (OpLayer r (ConsB (r0, head, elim) [])) lvl = Prelude.do
    pure (App r0 !(shuntHead ops head) !(shuntElim ops elim))
  shunt ops (OpLayer r (ConsA (_, op) [])) lvl = Prelude.do
    pure (App r (Var r op) [])
  shunt ops (InParens _ t) lvl = shunt ops t 0
  shunt ops tm@(OpLayer r layer) lvl = Prelude.do
    -- liftM $ write "ops: \{show (map toName ops)}"
    -- Shunt the *layer* at specified level by trying each operator from *ops* and making
    -- sure exactly one gets through.
    exactlyOne ops
   where
    none : List Operator -> Bool
    none [] = True
    none (o :: os) =
      case tryOp ops o r (forget layer) lvl of
        Left err => none os
        Right r => False

    exactlyOne : List Operator -> Either String OpFreeTerm
    exactlyOne [] = Left "No operators left to try out of \{map toName ops} at range \{show r} for term \{show tm}"
    exactlyOne (o :: os) =
      case tryOp ops o r (forget layer) lvl of
        Left err => exactlyOne os
        Right r => Id.do
          True <- none os
            | False => Left "Multiple alternatives pass through"
          pure (Right r)

  public export
  shuntTopLevel : List Operator -> TopLevel -> Either String OpFreeTopLevel
  shuntTopLevel ops (TypingSignature r x ty) = Prelude.do
    ty <- shunt ops ty 0
    pure (TypingSignature r x ty)
  shuntTopLevel ops (LetSignature r x ty rhs) = Prelude.do
    ty <- shunt ops ty 0
    rhs <- shunt ops rhs 0
    pure (LetSignature r x ty rhs)
  shuntTopLevel ops (DefineSignature r x ty rhs) = Prelude.do
    ty <- shunt ops ty 0
    rhs <- shunt ops rhs 0
    pure (DefineSignature r x ty rhs)
  shuntTopLevel ops (LetTypeSignature r x rhs) = Prelude.do
    rhs <- shunt ops rhs 0
    pure (LetTypeSignature r x rhs)
  shuntTopLevel ops (DefineTypeSignature r x rhs) = Prelude.do
    rhs <- shunt ops rhs 0
    pure (DefineTypeSignature r x rhs)
  shuntTopLevel ops (Syntax x y) = Left "Trying to shunt a syntax definition"
