module Nova.Surface.Parser

import Data.AlternatingList
import Data.AlternatingList1
import Data.AlternatingSnocList
import Data.AlternatingSnocList1
import Data.Fin
import Data.Location
import Data.Maybe
import Data.Util
import Data.Util
import Data.List.Elem


import Text.Lexing.Token
import public Text.Parsing.Fork

import Nova.Core.Name

import Nova.Surface.SemanticToken
import Nova.Surface.Language
import Nova.Surface.ParserGeneral
import Nova.Surface.ParserCategorical
import Nova.Surface.Operator


public export
Level : Type
Level = Fin 4

public export
zeroHead : Rule Head
zeroHead = do
  r <- specialAnn ElemAnn "Z"
  pure (NatVal0 r)

public export
oneValHead : Rule Head
oneValHead = do
  r <- specialAnn ElemAnn "tt"
  pure (OneVal r)

public export
underscoreHead : Rule Head
underscoreHead = do
  r <- specialAnn KeywordAnn "_"
  pure (Underscore r)

public export
boxHead : Rule Head
boxHead = do
  r <- specialAnn KeywordAnn "☐"
  pure (Box r)

public export
oneHead : Rule Head
oneHead = do
  r <- specialAnn ElemAnn "S"
  pure (NatVal1 r)

public export
natElimHead : Rule Head
natElimHead = do
  r <- specialAnn ElimAnn "ℕ-elim"
  pure (NatElim r)

public export
zeroElimHead : Rule Head
zeroElimHead = do
  r <- specialAnn ElimAnn "𝟘-elim"
  pure (ZeroElim r)

public export
natTyHead : Rule Head
natTyHead = do
  r <- specialAnn TypAnn "ℕ"
  pure (NatTy r)

public export
zeroTyHead : Rule Head
zeroTyHead = do
  r <- specialAnn TypAnn "𝟘"
  pure (ZeroTy r)

public export
oneTyHead : Rule Head
oneTyHead = do
  r <- specialAnn TypAnn "𝟙"
  pure (OneTy r)

public export
jHead : Rule Head
jHead = do
  r <- specialAnn ElimAnn "J"
  pure (EqElim r)

public export
universeTyHead : Rule Head
universeTyHead = do
  r <- specialAnn TypAnn "𝕌"
  pure (UniverseTy r)

public export
eqValHead : Rule Head
eqValHead = do
  r <- specialAnn ElemAnn "Refl"
  pure (EqVal r)

public export
varHead : Rule Head
varHead = do
  x <- located var
  pure (Var (fst x) (snd x))

public export
holeHead : Rule Head
holeHead = do
  l <- special "?"
  x <- located var
  appendSemanticToken (l + fst x, UnsolvedMetaAnn)
  pure (Hole (l + fst x) (snd x) Nothing)

public export
holeVarsHead : Rule Head
holeVarsHead = do
  l0 <- special "?"
  x <- var
  l1 <- special "("
  ls <- sepBy (optSpaceDelim *> delim "," <* optSpaceDelim) var
  l1 <- special ")"
  appendSemanticToken (l0 + l1, UnsolvedMetaAnn)
  pure (Hole (l0 + l1) x (Just ls))

public export
unnamedHoleVarsHead : Rule Head
unnamedHoleVarsHead = do
  l0 <- special "?"
  l0 <- special "("
  ls <- sepBy (optSpaceDelim *> delim "," <* optSpaceDelim) var
  l1 <- special ")"
  appendSemanticToken (l0 + l1, UnsolvedMetaAnn)
  pure (UnnamedHole (l0 + l1) (Just ls))

public export
unnamedHoleHead : Rule Head
unnamedHoleHead = do
  l <- specialAnn UnsolvedMetaAnn "?"
  pure (UnnamedHole l Nothing)

public export
unfoldHead : Rule Head
unfoldHead = do
  l <- special "!"
  x <- located var
  appendSemanticToken (l + fst x, ElemAnn)
  pure (Unfold (l + fst x) (snd x))

public export
piBetaHead : Rule Head
piBetaHead = do
  r <- specialAnn ElemAnn "Π-β"
  pure (PiBeta r)

public export
sigmaBeta1Head : Rule Head
sigmaBeta1Head = do
  r <- specialAnn ElemAnn "Σ-β₁"
  pure (SigmaBeta1 r)

public export
sigmaBeta2Head : Rule Head
sigmaBeta2Head = do
  r <- specialAnn ElemAnn "Σ-β₂"
  pure (SigmaBeta2 r)

public export
piEtaHead : Rule Head
piEtaHead = do
  r <- specialAnn ElemAnn "Π-η"
  pure (PiEta r)

public export
sigmaEtaHead : Rule Head
sigmaEtaHead = do
  r <- specialAnn ElemAnn "Σ-η"
  pure (SigmaEta r)

public export
natBetaZHead : Rule Head
natBetaZHead = do
  r <- specialAnn ElemAnn "ℕ-β-Z"
  pure (NatBetaZ r)

public export
natBetaSHead : Rule Head
natBetaSHead = do
  r <- specialAnn ElemAnn "ℕ-β-S"
  pure (NatBetaS r)

public export
piEqHead : Rule Head
piEqHead = do
  r <- specialAnn ElemAnn "Π⁼"
  pure (PiEq r)

public export
sigmaEqHead : Rule Head
sigmaEqHead = do
  r <- specialAnn ElemAnn "Σ⁼"
  pure (SigmaEq r)

public export
oneEqHead : Rule Head
oneEqHead = do
  r <- specialAnn ElemAnn "𝟙⁼"
  pure (OneEq r)

public export
elHead : Rule Head
elHead = do
  r <- specialAnn ElimAnn "El"
  pure (El r)

mutual
  public export
  head : Rule Head
  head = varHead
     <|> zeroHead
     <|> oneEqHead
     <|> oneHead
     <|> oneValHead
     <|> natElimHead
     <|> zeroElimHead
     <|> natBetaZHead
     <|> natBetaSHead
     <|> natTyHead
     <|> zeroTyHead
     <|> oneTyHead
     <|> universeTyHead
     <|> eqValHead
     <|> holeVarsHead
     <|> holeHead
     <|> unnamedHoleVarsHead
     <|> unnamedHoleHead
     <|> unfoldHead
     <|> piBetaHead
     <|> piEtaHead
     <|> piEqHead
     <|> sigmaBeta1Head
     <|> sigmaBeta2Head
     <|> sigmaEtaHead
     <|> sigmaEqHead
     <|> jHead
     <|> elHead
     <|> underscoreHead
     <|> boxHead

  public export
  head2 : Rule Head
  head2 = head <|> (inParentheses (located $ term 0) <&> uncurry Tm)

  public export
  section : Rule (Range, List1 VarName, Term)
  section = do
    l <- specialAnn TypAnn "("
    optSpaceDelim
    x <- sepBy1 spaceDelim varBound
    spaceDelim
    delim_ ":"
    mustWork $ do
      spaceDelim
      ty <- term 0
      optSpaceDelim
      r <- specialAnn TypAnn ")"
      pure (l + r, x, ty)

  public export
  implicitSection : Rule (Range, List1 VarName, Term)
  implicitSection = do
    l <- specialAnn TypAnn "{"
    optSpaceDelim
    x <- sepBy1 spaceDelim varBound
    spaceDelim
    specialAnn_ KeywordAnn ":"
    mustWork $ do
      spaceDelim
      ty <- term 0
      optSpaceDelim
      r <- specialAnn TypAnn "}"
      pure (l + r, x, ty)

  public export
  continuePi : (Range, Range, List1 VarName, Term) -> Rule Term
  continuePi (l, lx, x, a) = do
    spaceDelim
    exactAnn_ TypAnn "→"
    commit
    spaceDelim
    b <- located (term 0)
    pure (PiTy (l + fst b) x a (snd b))

  public export
  continueImplicitPi : (Range, Range, List1 VarName, Term) -> Rule Term
  continueImplicitPi (l, lx, x, a) = do
    spaceDelim
    exactAnn_ TypAnn "→"
    commit
    spaceDelim
    b <- located (term 0)
    pure (ImplicitPiTy (l + fst b) x a (snd b))

  public export
  continueSigma : (Range, Range, List1 VarName, Term) -> Rule Term
  continueSigma (l, lx, x, a) = do
    spaceDelim
    exactAnn_ TypAnn "⨯"
    commit
    spaceDelim
    b <- located (term 0)
    pure (SigmaTy (l + fst b) x a (snd b))

  public export
  piVal : Rule Term
  piVal = do
    x <- located (sepBy1 spaceDelim varBound)
    spaceDelim
    specialAnn_ ElemAnn "↦"
    commit
    spaceDelim
    f <- located (term 0)
    pure (PiVal (fst x + fst f) (snd x) (snd f))

  public export
  implicitPiVal : Rule Term
  implicitPiVal = do
    l0 <- specialAnn ElemAnn "{"
    x <- sepBy1 spaceDelim varBound
    specialAnn_ ElemAnn "}"
    spaceDelim
    specialAnn_ ElemAnn "↦"
    commit
    spaceDelim
    f <- located (term 0)
    pure (ImplicitPiVal (l0 + fst f) x (snd f))

  public export
  sectionBinder : Rule Term
  sectionBinder = do
    s <- located section
    continuePi s <|> continueSigma s

  public export
  implicitPi : Rule Term
  implicitPi = do
    s <- located implicitSection
    continueImplicitPi s

  public export
  app : Rule Term
  app = do
    (p0, h) <- located head2
    (p1, es) <- located elim
    guard "elimination spine must be non-empty" (length es > 0)
    pure (OpLayer (p0 + p1) (ConsB (p0 + p1, h, es) []))

  public export
  tactic : Rule Tactic

  public export
  tac : Rule Term
  tac = do
    l <- delim "tac"
    spaceDelim
    (r, alpha) <- located tactic
    pure (Tac (l + r) alpha)

  ||| Parse a Term exactly at level 3
  public export
  term3 : Rule Term
  term3 = app

  ||| Parse a Term exactly at level 3
  public export
  term4 : Rule Term
  term4 = (located head <&> (\(p, x) => OpLayer p (ConsB (p, x, []) [])))
      <|> inParentheses (term 0)

  public export
  simpleExpr : Rule (Range, Head, Elim)
  simpleExpr =
    (do
      (p0, h) <- located head2
      (p1, es) <- located elim
      guard "elimination spine must be non-empty" (length es > 0)
      pure (p0 + p1, h, es)
    )
     <|>
    (located head <&> (\(p, x) => (p, x, [])))
     <|>
    (located (inParentheses (term 0)) <&> (\(p, x) => (p, Tm p x, [])))

  public export
  simpleExprTerm : Rule Term
  simpleExprTerm = simpleExpr <&> (\(r, h, e) => OpLayer r (ConsB (r, h, e) []))

  public export
  continueSimpleExpr : AlternatingSnocList True (Range, String) (Range, Head, Elim)
                    -> Rule (AlternatingSnocList1 False (Range, String) (Range, Head, Elim))
  continueSimpleExpr list = do
    optSpaceDelim
    t <- simpleExpr
    pure (SnocB list t)

  public export
  continueOp : AlternatingSnocList False (Range, String) (Range, Head, Elim)
            -> Rule (AlternatingSnocList1 True (Range, String) (Range, Head, Elim))
  continueOp list = do
    optSpaceDelim
    t <- located op
    pure (SnocA list t)

  mutual
    public export
    continueManyTrue : AlternatingSnocList1 True (Range, String) (Range, Head, Elim) ->
                       Rule (k ** AlternatingSnocList1 k (Range, String) (Range, Head, Elim))
    continueManyTrue list = do
      (continueSimpleExpr (forget list) >>= continueManyFalse) <|> pure (_ ** list)

    public export
    continueManyFalse : AlternatingSnocList1 False (Range, String) (Range, Head, Elim) ->
                        Rule (k ** AlternatingSnocList1 k (Range, String) (Range, Head, Elim))
    continueManyFalse list = do
      (continueOp (forget list) >>= continueManyTrue) <|> pure (_ ** list)

  public export
  opLayerTrue : Rule (k ** AlternatingSnocList1 k (Range, String) (Range, Head, Elim))
  opLayerTrue = do
    s <- located op
    continueManyTrue (SnocA [<] s)

  public export
  opLayerFalse : Rule (k ** AlternatingSnocList1 k (Range, String) (Range, Head, Elim))
  opLayerFalse = do
    s <- simpleExpr
    continueManyFalse (SnocB [<] s)

  public export
  opLayer : Rule (k ** AlternatingSnocList1 k (Range, String) (Range, Head, Elim))
  opLayer = opLayerFalse <|> opLayerTrue

  public export
  opLayerTerm : Rule Term
  opLayerTerm = do
    (l, t) <- located opLayer
    pure (OpLayer l (snd $ toList1 $ snd t))

  ||| Parse a TypE at level ≥ n
  public export
  term : Level -> Rule Term
  term 0 = sectionBinder <|> implicitPi <|> piVal <|> implicitPiVal <|> tac <|> opLayerTerm
  term 1 =                                            opLayerTerm
  term 2 =                                            simpleExprTerm
  term 3 =                                            term4


  varBound : Rule VarName
  varBound = do
    x <- located var
    appendSemanticToken (fst x, BoundVarAnn)
    pure (snd x)

  public export
  termArg0 : Rule (List VarName, Term)
  termArg0 = do
    xs <- many (varBound <* delim "." <* optSpaceDelim)
    e <- term 0
    pure (xs, e)

  public export
  termArg1 : Rule (List VarName, Term)
  termArg1 = (term 3 <&> ([], )) <|> inParentheses termArg0

  public export
  termImplicitArg : Rule ElimEntry
  termImplicitArg = do
    delim_ "{"
    optSpaceDelim
    t <- term 0
    optSpaceDelim
    delim_ "}"
    pure (ImplicitArg t)

  public export
  elim : Rule Elim
  elim = many $ do
    spaceDelim
    located ((Arg <$> termArg1) <|> (Pi1 <$ delim_ ".π₁") <|> (Pi2 <$ delim_ ".π₂") <|> termImplicitArg)

  public export
  typingSignature : Rule TopLevel
  typingSignature = do
    l <- delim "assume"
    commit
    spaceDelim
    x <- located var
    appendSemanticToken (fst x, ElimAnn)
    spaceDelim
    delim_ ":"
    spaceDelim
    ty <- located (term 0)
    pure (TypingSignature (l + fst ty) (snd x) (snd ty))

  public export
  letSignature : Rule TopLevel
  letSignature = do
    l <- delim "let"
    commit
    spaceDelim
    x <- located var
    appendSemanticToken (fst x, ElimAnn)
    spaceDelim
    delim_ ":"
    spaceDelim
    ty <- term 0
    spaceDelim
    delim_ "≔"
    spaceDelim
    rhs <- located (term 0)
    pure (LetSignature (l + fst rhs) (snd x) ty (snd rhs))

  public export
  defineSignature : Rule TopLevel
  defineSignature = do
    l <- delim "define"
    commit
    spaceDelim
    x <- located var
    appendSemanticToken (fst x, ElimAnn)
    spaceDelim
    delim_ ":"
    spaceDelim
    ty <- term 0
    spaceDelim
    delim_ "≔"
    spaceDelim
    rhs <- located (term 0)
    pure (DefineSignature (l + fst rhs) (snd x) ty (snd rhs))


  namespace TopLevel
    public export
    continueLevel : AlternatingSnocList True String Nat
                 -> Rule (AlternatingSnocList1 False String Nat)
    continueLevel list = do
      spaceDelim
      exactAnn_ BoundVarAnn "e"
      n <- inBraces (delim_ "≥" *> withAnn ElemAnn nat)
      pure (SnocB list n)

    public export
    continueOp : AlternatingSnocList False String Nat
              -> Rule (AlternatingSnocList1 True String Nat)
    continueOp list = do
      spaceDelim
      t <- withAnn BoundVarAnn op
      pure (SnocA list t)

    mutual
      public export
      continueManyTrue : AlternatingSnocList1 True String Nat ->
                         Rule (k ** AlternatingSnocList1 k String Nat)
      continueManyTrue list = do
        (continueLevel (forget list) >>= continueManyFalse) <|> pure (_ ** list)

      public export
      continueManyFalse : AlternatingSnocList1 False String Nat ->
                          Rule (k ** AlternatingSnocList1 k String Nat)
      continueManyFalse list = do
        (continueOp (forget list) >>= continueManyTrue) <|> pure (_ ** list)

  public export
  opSyntaxTrue : Rule (k ** AlternatingSnocList1 k String Nat)
  opSyntaxTrue = do
    s <- withAnn BoundVarAnn op
    continueManyTrue (SnocA [<] s)

  public export
  opSyntaxFalse : Rule (k ** AlternatingSnocList1 k String Nat)
  opSyntaxFalse = do
    exactAnn_ BoundVarAnn "e"
    n <- inBraces (delim_ "≥" *> withAnn ElemAnn nat)
    continueManyFalse (SnocB [<] n)

  public export
  opSyntax : Rule (k ** AlternatingSnocList1 k String Nat)
  opSyntax = opSyntaxFalse <|> opSyntaxTrue

  public export
  syntax : Rule TopLevel
  syntax = do
    l <- delim "syntax"
    commit
    spaceDelim
    op <- opSyntax
    spaceDelim
    delim_ ":"
    spaceDelim
    exactAnn_ BoundVarAnn "e"
    n <- located (inBraces (withAnn ElemAnn nat))
    pure (Syntax (l + fst n) (MkOperator _ (snd $ toList1 $ snd op) (snd n)))

  public export
  topLevel : Rule TopLevel
  topLevel = typingSignature <|> letSignature <|> defineSignature <|> syntax

  public export
  surfaceFile : Rule (List1 TopLevel)
  surfaceFile = do
    sepBy1 spaceDelimDef topLevel

mutual
  tactic = composition <|> split <|> exact <|> unfold <|> id <|> trivial <|> rewriteInv <|> let' <|> rewrite'

  public export
  compositionArg : Rule Tactic
  compositionArg = split <|> exact <|> unfold <|> id <|> trivial <|> rewriteInv <|> let' <|> rewrite'

  ensureColumn : (col : Int) -> Rule a -> Rule a
  ensureColumn col f = do
    (r, t) <- located f
    guard "wrong column" (snd r.start == col)
    pure t

  continueComposition : (column : Int) -> Rule (List Tactic)
  continueComposition column = do
    [| (spaceDelim *> compositionArg <* delim_ ";") :: continueComposition column |] <|> pure []

  public export
  composition : Rule Tactic
  composition = do
    (l, t) <- located compositionArg
    delim_ ";"
    (r, rest) <- located (continueComposition (snd l.start))
    pure (Composition (l + r) (t ::: rest))

  public export
  id : Rule Tactic
  id = delim "id" <&> Id

  public export
  trivial : Rule Tactic
  trivial = delim "trivial" <&> Trivial

  public export
  exact : Rule Tactic
  exact = do
    l <- delim "exact"
    spaceDelim
    (r, tm) <- located (term 0)
    pure (Exact (l + r) tm)

  public export
  unfold : Rule Tactic
  unfold = do
    l <- delim "unfold"
    spaceDelim
    (r, tm) <- located (term 0)
    pure (Unfold (l + r) tm)

  continueSplit : (col : Int) -> Rule (List Tactic)
  continueSplit col = do
    [| (spaceDelim *> delim "*" *> spaceDelim *> tactic) :: continueSplit col |] <|> pure []

  public export
  split : Rule Tactic
  split = do
    l <- delim "*"
    spaceDelim
    alpha <- tactic
    (r, alphas) <- located $ continueSplit (snd l.start)
    let (as, a) = toSnocList1 $ alpha ::: alphas
    pure (Split (l + r) as a)

  public export
  rewriteInv : Rule Tactic
  rewriteInv = do
    l <- delim "rewrite⁻¹"
    spaceDelim
    rho <- term 3
    spaceDelim
    e <- located (term 3)
    pure (RewriteInv (l + fst e) rho (snd e))

  public export
  let' : Rule Tactic
  let' = do
    l <- delim "let"
    spaceDelim
    x <- var
    spaceDelim
    delim_ "≔"
    spaceDelim
    e <- located (term 0)
    pure (Let (l + fst e) x (snd e))

  public export
  rewrite' : Rule Tactic
  rewrite' = do
    l <- delim "rewrite"
    spaceDelim
    rho <- term 3
    spaceDelim
    e <- located (term 3)
    pure (Rewrite (l + fst e) rho (snd e))
