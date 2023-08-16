module ETT.Surface.Shunting

import Data.Location

import Data.AlternatingList
import Data.AlternatingList1
import Data.AlternatingSnocList
import Data.AlternatingSnocList1

import ETT.Core.Name
import ETT.Core.Monad

import ETT.Surface.Language
import ETT.Surface.Operator

-- 5 + 5
-- a + b + c + d

-- *) a/5, (b + c + d)/5
-- *) (a + b)/5, (c + d)/5
-- *) (a + b + c)/5, d/5

-- 5 + 5 + 5
-- a + b + c + d

-- *) a/5, (b + c + d)/(5 + 5)
--    *) a/5, b/5, (c + d)/5
--    *) a/5, (b + c)/5, d/5
-- *) (a + b)/5, (c + d)/(5 + 5)
--    *) (a + b)/5, c/5, d/5
-- *) (a + b + c)/5, d/(5 + 5)
--    (a + b + c)/5, ∅

-- - 2

-- - x + if x then - x else - 2

-- if 2 then 2

-- if x then true else if x then false else true

-- 2 then

-- (x) then (true else if x then false else true)
-- (x then true else if x) then (false else true)



-- op ...

-- app []

-- app op ...

-- []

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
match (ConsB app (ConsA op rest)) layer = do
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

processApp : Range -> String -> List OpFreeTerm -> Mb OpFreeTerm
processApp r "_≡_∈_" [a, b, ty] = return (EqTy r a b ty)
processApp r "_⨯_" [a, b] = return (ProdTy r a b)
processApp r "_,_" [a, b] = return (SigmaVal r a b)
processApp r "_→_" [a, b] = return (FunTy r a b)
processApp r op list = return (App r (Var r op) (map (\t => Arg ([], t)) list))

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
       -> Mb OpFreeTerm
  tryOp ops op@(MkOperator k seq oplvl) range layer lvl = M.do
    case (oplvl >= lvl) of
      False => nothing
      True => M.do
        r <- forList (match (forget seq) layer) $ \list => M.do
          forList list $ \(n, layer) =>
            case layer of
              (_ ** []) => M.do
                M.return Nothing
              (_ ** ConsA x smth) => shunt ops (OpLayer (getRange (ConsA x smth)) (ConsA x smth)) n
              (_ ** ConsB x smth) => shunt ops (OpLayer (getRange (ConsB x smth)) (ConsB x smth)) n
        write "Trying op:"
        write (toName op)
        write "\{show r}"
        let r = map sequence r
        write "\{show r}"
        let Just r = exactlyOne r
             | Nothing => nothing
        write "\{show r}"
        processApp range (toName op) r
   where
    none : List (Maybe a) -> Bool
    none [] = True
    none (Nothing :: rest) = none rest
    none (Just _ :: rest) = False

    exactlyOne : List (Maybe a) -> Maybe a
    exactlyOne [] = Nothing
    exactlyOne (Just x :: rest) =
      case none rest of
        True => Just x
        False => Nothing
    exactlyOne (Nothing :: rest) = exactlyOne rest

  public export
  shuntElimEntry : List Operator -> ElimEntry -> Mb OpFreeElimEntry
  shuntElimEntry ops (Arg (xs, t)) = Mb.do
    return (Arg (xs, !(shunt ops t 0)))
  shuntElimEntry ops Pi1 = Mb.do
    return Pi1
  shuntElimEntry ops Pi2 = Mb.do
    return Pi2
  shuntElimEntry ops (ImplicitArg t) = Mb.do
    return (ImplicitArg !(shunt ops t 0))

  public export
  shuntElim : List Operator -> Elim -> Mb OpFreeElim
  shuntElim ops [] = Mb.do
    return []
  shuntElim ops (e :: es) = Mb.do
    e <- shuntElimEntry ops e
    es <- shuntElim ops es
    return (e :: es)

  public export
  shuntHead : List Operator -> Head -> Mb OpFreeHead
  shuntHead ops (Var x str) = return (Var x str)
  shuntHead ops (NatVal0 x) = return (NatVal0 x)
  shuntHead ops (NatVal1 x) = return (NatVal1 x)
  shuntHead ops (NatElim x) = return (NatElim x)
  shuntHead ops (EqElim x) = return (EqElim x)
  shuntHead ops (EqVal x) = return (EqVal x)
  shuntHead ops (NatTy x) = return (NatTy x)
  shuntHead ops (UniverseTy x) = return (UniverseTy x)
  shuntHead ops (Hole x str mstrs) = return (Hole x str mstrs)
  shuntHead ops (UnnamedHole x mstrs) = return (UnnamedHole x mstrs)
  shuntHead ops (Unfold x str) = return (Unfold x str)
  shuntHead ops (PiBeta x) = return (PiBeta x)
  shuntHead ops (PiEta x) = return (PiEta x)
  shuntHead ops (NatBetaZ x) = return (NatBetaZ x)
  shuntHead ops (NatBetaS x) = return (NatBetaS x)
  shuntHead ops (PiEq x) = return (PiEq x)
  shuntHead ops (Tm r tm) = Mb.do
    return (Tm r !(shunt ops tm 0))

  ||| Shunt the given term at the specified *lvl*.
  public export
  shunt : List Operator -> Term -> (lvl : Nat) -> Mb OpFreeTerm
  shunt ops (PiTy r x dom cod) lvl = Mb.do
    case (lvl > 0) of
      True => nothing
      False => Mb.do
       dom <- shunt ops dom 0
       cod <- shunt ops cod 0
       return (PiTy r x dom cod)
  shunt ops (ImplicitPiTy r x dom cod) lvl = Mb.do
    case (lvl > 0) of
      True => nothing
      False => Mb.do
        dom <- shunt ops dom 0
        cod <- shunt ops cod 0
        return (ImplicitPiTy r x dom cod)
  shunt ops (SigmaTy r x dom cod) lvl = Mb.do
    case (lvl > 0) of
      True => nothing
      False => Mb.do
       dom <- shunt ops dom 0
       cod <- shunt ops cod 0
       return (SigmaTy r x dom cod)
  shunt ops (PiVal r x f) lvl = Mb.do
    case (lvl > 0) of
      True => nothing
      False => Mb.do
       f <- shunt ops f 0
       return (PiVal r x f)
  shunt ops (ImplicitPiVal r x f) lvl = Mb.do
    case (lvl > 0) of
      True => nothing
      False => Mb.do
       f <- shunt ops f 0
       return (ImplicitPiVal r x f)
  shunt ops (OpLayer r (ConsB (r0, head, elim) [])) lvl = Mb.do
    return (App r0 !(shuntHead ops head) !(shuntElim ops elim))
  shunt ops (OpLayer r (ConsA (_, op) [])) lvl = Mb.do
    return (App r (Var r op) [])
  shunt ops (OpLayer r layer) lvl = Mb.do
    liftM $ write "ops: \{show (map toName ops)}"
    -- Shunt the *layer* at specified level by trying each operator from *ops* and making
    -- sure exactly one gets through.
    exactlyOne ops
   where
    none : List Operator -> M Bool
    none [] = return True
    none (o :: os) = M.do
      case !(tryOp ops o r (forget layer) lvl) of
        Nothing => none os
        Just r => return False

    exactlyOne : List Operator -> Mb OpFreeTerm
    exactlyOne [] = nothing
    exactlyOne (o :: os) = M.do
      case !(tryOp ops o r (forget layer) lvl) of
        Nothing => exactlyOne os
        Just r => M.do
          True <- none os
            | False => nothing
          return (Just r)

  public export
  shuntTopLevel : List Operator -> TopLevel -> Mb OpFreeTopLevel
  shuntTopLevel ops (TypingSignature r x ty) = Mb.do
    ty <- shunt ops ty 0
    return (TypingSignature r x ty)
  shuntTopLevel ops (LetSignature r x ty rhs) = Mb.do
    ty <- shunt ops ty 0
    rhs <- shunt ops rhs 0
    return (LetSignature r x ty rhs)
  shuntTopLevel ops (Syntax x y) = nothing

