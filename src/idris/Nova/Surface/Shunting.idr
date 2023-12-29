module Nova.Surface.Shunting

import Data.Location
import Data.List1
import Data.Interpolation

import Data.AlternatingList
import Data.AlternatingList1
import Data.AlternatingSnocList
import Data.AlternatingSnocList1

import Nova.Core.Name
import Nova.Core.Monad

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
       -> M (Either String OpFreeTerm)
  tryOp ops op@(MkOperator k seq oplvl) range layer lvl = M.do
    case (oplvl >= lvl) of
      False => error "\{toName op}'s level is \{show oplvl} but the target lvl is ≥\{show lvl}"
      True => M.do
        r <- forList (match (forget seq) layer) $ \list => M.do
          forList list $ \(n, layer) =>
            case layer of
              (_ ** []) => M.do
                M.return (Left "Nothing to parse at target level \{show n}")
              (_ ** ConsA x smth) => shunt ops (OpLayer (getRange (ConsA x smth)) (ConsA x smth)) n
              (_ ** ConsB x smth) => shunt ops (OpLayer (getRange (ConsB x smth)) (ConsB x smth)) n
        {- write "Trying op:"
        write (toName op)
        write "\{show r}" -}
        let r = map sequence r
        -- write "\{show r}"
        let Right r = exactlyOne r
             | Left err => error err
        -- write "\{show r}"
        return $ Right $ processApp range (toName op) r
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
  shuntElimEntry : List Operator -> ElimEntry -> M (Either String OpFreeElimEntry)
  shuntElimEntry ops (Arg (xs, t)) = MEither.do
    return (Arg (xs, !(shunt ops t 0)))
  shuntElimEntry ops Pi1 = MEither.do
    return Pi1
  shuntElimEntry ops Pi2 = MEither.do
    return Pi2
  shuntElimEntry ops (ImplicitArg t) = MEither.do
    return (ImplicitArg !(shunt ops t 0))

  public export
  shuntElim : List Operator -> Elim -> M (Either String OpFreeElim)
  shuntElim ops [] = MEither.do
    return []
  shuntElim ops ((r, e) :: es) = MEither.do
    e <- shuntElimEntry ops e
    es <- shuntElim ops es
    return ((r, e) :: es)

  public export
  shuntHead : List Operator -> Head -> M (Either String OpFreeHead)
  shuntHead ops (Var x str) = return (Var x str)
  shuntHead ops (NatVal0 x) = return (NatVal0 x)
  shuntHead ops (NatVal1 x) = return (NatVal1 x)
  shuntHead ops (OneVal x) = return (OneVal x)
  shuntHead ops (NatElim x) = return (NatElim x)
  shuntHead ops (ZeroElim x) = return (ZeroElim x)
  shuntHead ops (EqElim x) = return (EqElim x)
  shuntHead ops (EqVal x) = return (EqVal x)
  shuntHead ops (NatTy x) = return (NatTy x)
  shuntHead ops (ZeroTy x) = return (ZeroTy x)
  shuntHead ops (OneTy x) = return (OneTy x)
  shuntHead ops (UniverseTy x) = return (UniverseTy x)
  shuntHead ops (Hole x str mstrs) = return (Hole x str mstrs)
  shuntHead ops (UnnamedHole x mstrs) = return (UnnamedHole x mstrs)
  shuntHead ops (Unfold x str) = return (Unfold x str)
  shuntHead ops (PiBeta x) = return (PiBeta x)
  shuntHead ops (PiEta x) = return (PiEta x)
  shuntHead ops (PiEq x) = return (PiEq x)
  shuntHead ops (SigmaBeta1 x) = return (SigmaBeta1 x)
  shuntHead ops (SigmaBeta2 x) = return (SigmaBeta2 x)
  shuntHead ops (SigmaEta x) = return (SigmaEta x)
  shuntHead ops (SigmaEq x) = return (SigmaEq x)
  shuntHead ops (NatBetaZ x) = return (NatBetaZ x)
  shuntHead ops (NatBetaS x) = return (NatBetaS x)
  shuntHead ops (OneEq x) = return (OneEq x)
  shuntHead ops (El x) = return (El x)
  shuntHead ops (Underscore x) = return (Underscore x)
  shuntHead ops (Box x) = return (Box x)
  shuntHead ops (Tm r tm) = MEither.do
    return (Tm r !(shunt ops tm 0))

  public export
  shuntTactic : List Operator -> Tactic -> M (Either String OpFreeTactic)
  shuntTactic ops (Id x) = return (Id x)
  shuntTactic ops (Trivial x) = return (Trivial x)
  shuntTactic ops (Composition r alphas) = MEither.do
    alphas <- forList1 alphas (shuntTactic ops)
    return (Composition r alphas)
  shuntTactic ops (Unfold r tm) = MEither.do
    tm <- shunt ops tm 0
    return (Unfold r tm)
  shuntTactic ops (Exact r tm) = MEither.do
    tm <- shunt ops tm 0
    return (Exact r tm)
  shuntTactic ops (Split r alphas beta) = MEither.do
    alphas <- forSnocList alphas (shuntTactic ops)
    beta <- shuntTactic ops beta
    return (Split r alphas beta)
  shuntTactic ops (RewriteInv r a b) = MEither.do
    a <- shunt ops a 3
    b <- shunt ops b 3
    return (RewriteInv r a b)
  shuntTactic ops (Rewrite r a b) = MEither.do
    a <- shunt ops a 3
    b <- shunt ops b 3
    return (Rewrite r a b)
  shuntTactic ops (Let r x e) = MEither.do
    e <- shunt ops e 0
    return (Let r x e)
  shuntTactic ops (NormaliseCommutativeMonoid r a o b) = MEither.do
    a <- shunt ops a 3
    b <- shunt ops b 3
    return (NormaliseCommutativeMonoid r a o b)

  ||| Shunt the given term at the specified *lvl*.
  public export
  shunt : List Operator -> Term -> (lvl : Nat) -> M (Either String OpFreeTerm)
  shunt ops (PiTy r (x ::: []) dom cod) lvl = MEither.do
    case (lvl > 0) of
      True => error "Can't parse (_ : _) → _ at level \{show lvl}"
      False => MEither.do
       dom <- shunt ops dom 0
       cod <- shunt ops cod 0
       return (PiTy r x dom cod)
  shunt ops (PiTy r (x ::: y :: zs) dom cod) lvl = MEither.do
    case (lvl > 0) of
      True => error "Can't parse (_ : _) → _ at level \{show lvl}"
      False => MEither.do
       dom' <- shunt ops dom 0
       cod' <- shunt ops (PiTy r (y ::: zs) dom cod) 0
       return (PiTy r x dom' cod')
  shunt ops (ImplicitPiTy r (x ::: []) dom cod) lvl = MEither.do
    case (lvl > 0) of
      True => error "Can't parse {_ : _} → _ at level \{show lvl}"
      False => MEither.do
        dom <- shunt ops dom 0
        cod <- shunt ops cod 0
        return (ImplicitPiTy r x dom cod)
  shunt ops (ImplicitPiTy r (x ::: y :: zs) dom cod) lvl = MEither.do
    case (lvl > 0) of
      True => error "Can't parse {_ : _} → _ at level \{show lvl}"
      False => MEither.do
        dom' <- shunt ops dom 0
        cod' <- shunt ops (ImplicitPiTy r (y ::: zs) dom cod) 0
        return (ImplicitPiTy r x dom' cod')
  shunt ops (SigmaTy r (x ::: []) dom cod) lvl = MEither.do
    case (lvl > 0) of
      True => error "Can't parse (_ : _) ⨯ _ at level \{show lvl}"
      False => MEither.do
       dom <- shunt ops dom 0
       cod <- shunt ops cod 0
       return (SigmaTy r x dom cod)
  shunt ops (SigmaTy r (x ::: y :: zs) dom cod) lvl = MEither.do
    case (lvl > 0) of
      True => error "Can't parse (_ : _) ⨯ _ at level \{show lvl}"
      False => MEither.do
       dom' <- shunt ops dom 0
       cod' <- shunt ops (SigmaTy r (y ::: zs) dom cod) 0
       return (SigmaTy r x dom' cod')
  shunt ops (PiVal r (x ::: []) f) lvl = MEither.do
    case (lvl > 0) of
      True => error "Can't parse _ ↦ _ at level \{show lvl}"
      False => MEither.do
       f <- shunt ops f 0
       return (PiVal r x f)
  shunt ops (PiVal r (x ::: y :: zs) f) lvl = MEither.do
    case (lvl > 0) of
      True => error "Can't parse _ ↦ _ at level \{show lvl}"
      False => MEither.do
       f' <- shunt ops (PiVal r (y ::: zs) f) 0
       return (PiVal r x f')
  shunt ops (ImplicitPiVal r (x ::: []) f) lvl = MEither.do
    case (lvl > 0) of
      True => error "Can't parse {_} ↦ _ at level \{show lvl}"
      False => MEither.do
       f <- shunt ops f 0
       return (ImplicitPiVal r x f)
  shunt ops (ImplicitPiVal r (x ::: y :: zs) f) lvl = MEither.do
    case (lvl > 0) of
      True => error "Can't parse {_} ↦ _ at level \{show lvl}"
      False => MEither.do
       f' <- shunt ops (ImplicitPiVal r (y ::: zs) f) 0
       return (ImplicitPiVal r x f')
  shunt ops (Tac r alpha) lvl = MEither.do
    case (lvl > 0) of
      True => error "Can't parse tac ... at level \{show lvl}"
      False => MEither.do
        alpha <- shuntTactic ops alpha
        return (Tac r alpha)
  shunt ops (OpLayer r (ConsB (r0, head, elim) [])) lvl = MEither.do
    return (App r0 !(shuntHead ops head) !(shuntElim ops elim))
  shunt ops (OpLayer r (ConsA (_, op) [])) lvl = MEither.do
    return (App r (Var r op) [])
  shunt ops tm@(OpLayer r layer) lvl = MEither.do
    -- liftM $ write "ops: \{show (map toName ops)}"
    -- Shunt the *layer* at specified level by trying each operator from *ops* and making
    -- sure exactly one gets through.
    exactlyOne ops
   where
    none : List Operator -> M Bool
    none [] = return True
    none (o :: os) = M.do
      case !(tryOp ops o r (forget layer) lvl) of
        Left err => none os
        Right r => return False

    exactlyOne : List Operator -> M (Either String OpFreeTerm)
    exactlyOne [] = error "No operators left to try out of \{map toName ops} at range \{show r} for term \{show tm}"
    exactlyOne (o :: os) = M.do
      case !(tryOp ops o r (forget layer) lvl) of
        Left err => exactlyOne os
        Right r => M.do
          True <- none os
            | False => error "Multiple alternatives pass through"
          return (Right r)

  public export
  shuntTopLevel : List Operator -> TopLevel -> M (Either String OpFreeTopLevel)
  shuntTopLevel ops (TypingSignature r x ty) = MEither.do
    ty <- shunt ops ty 0
    return (TypingSignature r x ty)
  shuntTopLevel ops (LetSignature r x ty rhs) = MEither.do
    ty <- shunt ops ty 0
    rhs <- shunt ops rhs 0
    return (LetSignature r x ty rhs)
  shuntTopLevel ops (DefineSignature r x ty rhs) = MEither.do
    ty <- shunt ops ty 0
    rhs <- shunt ops rhs 0
    return (DefineSignature r x ty rhs)
  shuntTopLevel ops (LetTypeSignature r x rhs) = MEither.do
    rhs <- shunt ops rhs 0
    return (LetTypeSignature r x rhs)
  shuntTopLevel ops (DefineTypeSignature r x rhs) = MEither.do
    rhs <- shunt ops rhs 0
    return (DefineTypeSignature r x rhs)
  shuntTopLevel ops (Syntax x y) = error "Trying to shunt a syntax definition"
