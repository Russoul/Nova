module ETT.Core.Pretty

import Control.Monad.FailSt

import Data.Fin
import Data.String
import Data.Util

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import ETT.Core.Language
import ETT.Core.Substitution

-- (x : A{≥0}) → A{≥0}
-- e{≥3} ≡ e{≥3} ∈ e{≥0}
-- El e{≥4}

-- x ↦ e{≥0}
-- S e{≥4}

public export
data Ann = Keyword | ContextVar | SignatureVar | Form | Elim | Intro

public export
parens' : Doc Ann -> Doc Ann
parens' = enclose (annotate Keyword lparen) (annotate Keyword rparen)

public export
brackets' : Doc Ann -> Doc Ann
brackets' = enclose (annotate Keyword lbracket) (annotate Keyword rbracket)

Level = Fin 5

wrapTypE : TypE -> Level -> Doc Ann -> M (Doc Ann)
wrapTypE (PiTy {}) lvl doc =
  case lvl <= 0 of
    True => return doc
    False => return (parens' doc)
wrapTypE tm@(ContextSubstElim {}) lvl doc =
  wrapTypE (runSubst tm) lvl doc
wrapTypE tm@(SignatureSubstElim {}) lvl doc =
  wrapTypE (runSubst tm) lvl doc
wrapTypE (EqTy l r ty) lvl doc =
  case lvl <= 1 of
    True => return doc
    False => return (parens' doc)
wrapTypE NatTy lvl doc = return doc
wrapTypE UniverseTy lvl doc = return doc
wrapTypE (SignatureVarElim k _) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapTypE (El x) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)

wrapElem : Elem -> Level -> Doc Ann -> M (Doc Ann)
wrapElem (PiTy {}) lvl doc =
  case lvl <= 0 of
    True => return doc
    False => return (parens' doc)
wrapElem (PiVal {}) lvl doc =
  case lvl <= 0 of
    True => return doc
    False => return (parens' doc)
wrapElem (PiElim {}) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapElem NatVal0 lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapElem (NatVal1 x) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapElem NatTy lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapElem (NatElim str x y str1 str2 z w) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapElem tm@(ContextSubstElim {}) lvl doc = wrapElem (runSubst tm) lvl doc
wrapElem tm@(SignatureSubstElim {}) lvl doc = wrapElem (runSubst tm) lvl doc
wrapElem (ContextVarElim {}) lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapElem (SignatureVarElim {}) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapElem (EqTy {}) lvl doc =
  case lvl <= 1 of
    True => return doc
    False => return (parens' doc)
wrapElem (EqVal {}) lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapElem (EqElim {}) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)

||| Examples:
||| i .j. ⊦ j
||| i .j. k ⊦ j
||| i i .i. ⊦ i
||| i .i. i ⊦ i{1}
||| .i. i i ⊦ i{2}
||| .i. i a b c d i ⊦ i{2}
||| That is: we render the "root" of the name,
||| and its de-bruijn index w.r.t. all names in the *same context*
||| that have the *same root*.
public export
localise : SnocList VarName -> Nat -> M (VarName, Nat)
localise [<] idx = throw "Exception in 'localise'"
localise (xs :< x) Z = return (x, 0)
localise (xs :< x) (S k) = FailSt.do
  (name, idx) <- localise xs k
  case name == x of
    True => return (name, S idx)
    False => return (name, idx)

public export
prettySignatureVar : SnocList VarName -> Nat -> M (Doc Ann)
prettySignatureVar sig i = FailSt.do
  -- return (annotate SignatureVar (pretty $ "χ" ++ natToSuperscript i))
  (n, 0) <- localise sig i
    | (n, k) =>
        return (annotate SignatureVar (pretty n <+> "{" <+> pretty k <+> "}"))
  return (annotate SignatureVar (pretty n))

public export
prettyContextVar : SnocList VarName -> Nat -> M (Doc Ann)
prettyContextVar sig i = FailSt.do
  -- return (annotate SignatureVar (pretty $ "x" ++ natToSuperscript i))
  (n, 0) <- localise sig i
    | (n, k) =>
        return (annotate ContextVar (pretty n <+> "{" <+> pretty k <+> "}"))
  return (annotate ContextVar (pretty n))

mutual
  public export
  prettySubstContextNu' : SnocList VarName -> SnocList VarName -> SubstContextNF -> M (Doc Ann)
  prettySubstContextNu' sig ctx (WkN k) = return (pretty "↑\{natToSuperscript k}")
  prettySubstContextNu' sig ctx (Ext sigma t) = return $ parens' $
    !(prettySubstContext' sig ctx sigma)
     <+>
    annotate Keyword ","
     <++>
    !(prettyElem sig ctx t 0)
  prettySubstContextNu' sig ctx Terminal = return "·"

  public export
  prettySubstContext' : SnocList VarName -> SnocList VarName -> SubstContext -> M (Doc Ann)
  prettySubstContext' sig ctx sigma = prettySubstContextNu' sig ctx (eval sigma)

  public export
  prettySubstContext : SnocList VarName -> SnocList VarName -> SubstContext -> M (Doc Ann)
  prettySubstContext sig ctx sigma = prettySubstContext' sig ctx sigma

  prettyTypE' : SnocList VarName
             -> SnocList VarName
             -> TypE
             -> M (Doc Ann)
  prettyTypE' sig ctx (PiTy x dom cod) = FailSt.do
    return $
      annotate Form lparen
       <+>
      annotate ContextVar (pretty x)
       <++>
      annotate Keyword ":"
       <++>
      !(prettyTypE sig ctx dom 0)
       <+>
      annotate Form rparen
       <++>
      annotate Keyword "→"
       <++>
      !(prettyTypE sig (ctx :< x) cod 0)
  prettyTypE' sig ctx tm@(ContextSubstElim {}) =
   prettyTypE' sig ctx (runSubst tm)
  prettyTypE' sig ctx tm@(SignatureSubstElim {}) =
   prettyTypE' sig ctx (runSubst tm)
  prettyTypE' sig ctx (EqTy l r ty) = return $
    !(prettyElem sig ctx l 3)
     <++>
    annotate Form "≡"
     <++>
    !(prettyElem sig ctx r 3)
     <++>
    annotate Form "∈"
     <++>
    !(prettyTypE sig ctx ty 0)
  prettyTypE' sig ctx NatTy =
    return $ annotate Form "ℕ"
  prettyTypE' sig ctx UniverseTy =
    return $ annotate Form "𝕌"
  prettyTypE' sig ctx (SignatureVarElim k sigma) = FailSt.do
    x <- prettySignatureVar sig k
    return $
      x
       <+>
      parens' !(prettySubstContext sig ctx sigma)
  prettyTypE' sig ctx (El e) = FailSt.do
    return $
      annotate Form "El"
       <++>
      !(prettyElem sig ctx e 4)

  public export
  prettyTypE : SnocList VarName
            -> SnocList VarName
            -> TypE
            -> Level
            -> M (Doc Ann)
  prettyTypE sig ctx tm lvl =
    wrapTypE tm lvl !(prettyTypE' sig ctx tm)

  public export
  prettyElem' : SnocList VarName
             -> SnocList VarName
             -> Elem
             -> M (Doc Ann)
  prettyElem' sig ctx (PiTy x dom cod) =
    return $
      annotate Intro lparen
       <+>
      annotate ContextVar (pretty x)
       <++>
      annotate Keyword ":"
       <++>
      !(prettyElem sig ctx dom 0)
       <+>
      annotate Intro rparen
       <++>
      annotate Keyword "→"
       <++>
      !(prettyElem sig (ctx :< x) cod 0)
  prettyElem' sig ctx (PiVal x _ _ f) =
    return $
      annotate ContextVar (pretty x)
       <++>
      annotate Intro "↦"
       <++>
      !(prettyElem sig (ctx :< x) f 0)
  prettyElem' sig ctx (PiElim f x a b e) =
    return $
      !(prettyElem sig ctx f 3)
       <++>
      !(prettyElem sig ctx e 4)
  prettyElem' sig ctx NatVal0 =
    return $ annotate Intro "0"
  prettyElem' sig ctx (NatVal1 e) = return $
    annotate Intro "S"
      <++>
    !(prettyElem sig ctx e 4)
  prettyElem' sig ctx NatTy =
    return $ annotate Intro "ℕ"
  prettyElem' sig ctx (NatElim x schema z y h s t) = FailSt.do
    return $
      annotate Elim "ℕ-elim"
       <++>
      parens' (annotate ContextVar (pretty x) <+> annotate Keyword "." <++> !(prettyTypE sig (ctx :< x) schema 0))
       <++>
      !(prettyElem sig ctx z 4)
       <++>
      parens' (annotate ContextVar (pretty y)
                <+>
               annotate Keyword "."
                <+>
               annotate ContextVar (pretty h)
                <+>
               annotate Keyword "."
                <++>
               !(prettyElem sig (ctx :< y :< h) s 0)
              )
       <++>
      !(prettyElem sig ctx t 4)
  prettyElem' sig ctx tm@(ContextSubstElim {}) =
    prettyElem' sig ctx (runSubst tm)
  prettyElem' sig ctx tm@(SignatureSubstElim {}) =
    prettyElem' sig ctx (runSubst tm)
  prettyElem' sig ctx (ContextVarElim k) =
    prettyContextVar ctx k
  prettyElem' sig ctx (SignatureVarElim k sigma) = FailSt.do
    x <- prettySignatureVar sig k
    return $
      x
       <+>
      parens' !(prettySubstContext sig ctx sigma)
  prettyElem' sig ctx (EqTy l r ty) = return $
    !(prettyElem sig ctx l 3)
     <++>
    annotate Form "≡"
     <++>
    !(prettyElem sig ctx r 3)
     <++>
    annotate Form "∈"
     <++>
    !(prettyElem sig ctx ty 0)
  prettyElem' sig ctx EqVal =
    return $ annotate Intro "*"
  prettyElem' sig ctx (EqElim ty a0 x h schema r a1 a) = FailSt.do
    return $
      annotate Elim "J"
       <++>
      !(prettyTypE sig ctx ty 4)
       <++>
      !(prettyElem sig ctx a0 4)
       <++>
      parens' (annotate ContextVar (pretty x)
                <+>
               annotate Keyword "."
                <+>
               annotate ContextVar (pretty h)
                <+>
               annotate Keyword "."
                <++>
               !(prettyTypE sig (ctx :< x :< h) schema 0)
              )
       <++>
      !(prettyElem sig ctx r 4)
       <++>
      !(prettyElem sig ctx a1 4)
       <++>
      !(prettyElem sig ctx a 4)

  public export
  prettyElem : SnocList VarName
            -> SnocList VarName
            -> Elem
            -> Level
            -> M (Doc Ann)
  prettyElem sig ctx tm lvl =
    wrapElem tm lvl !(prettyElem' sig ctx tm)

  tail : Context -> SnocList (VarName, TypE)
  tail Empty = [<]
  tail (SignatureVarElim {}) = [<]
  tail (Ext tyes x ty) = tail tyes :< (x, ty)

  head : Context -> Either () Nat
  head Empty = Left ()
  head (SignatureVarElim x) = Right x
  head (Ext tyes x ty) = head tyes

  public export
  prettyTelescope : SnocList VarName
                 -> SnocList VarName
                 -> List (VarName, TypE)
                 -> M (Doc Ann)
  prettyTelescope sig ctx [] = return ""
  prettyTelescope sig ctx ((x, ty) :: tyes) = return $
    lparen
     <+>
    annotate ContextVar (pretty x)
     <++>
    annotate Keyword ":"
     <++>
    !(prettyTypE sig ctx ty 0)
     <+>
    rparen
     <++>
    !(prettyTelescope sig (ctx :< x) tyes)

  public export
  prettyContext : SnocList VarName
               -> Context
               -> M (Doc Ann)
  prettyContext sig ctx =
    case head ctx of
      Left () => prettyTelescope sig [<] (cast $ tail ctx)
      Right x => return $
        !(prettySignatureVar sig x) <++> !(prettyTelescope sig [<] (cast $ tail ctx))

  public export
  prettySignatureEntry : SnocList VarName -> VarName -> SignatureEntry -> M (Doc Ann)
   -- χ ctx
   -- Γ ⊦ χ type
   -- Γ ⊦ χ : A
   -- Γ ⊦ χ ≔ e : A
  prettySignatureEntry sig x CtxEntry = return (pretty x <++> annotate Keyword "ctx")
  prettySignatureEntry sig x (TypEEntry ctx) = return $
    !(prettyContext sig ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    annotate ContextVar (pretty x)
     <++>
    annotate Keyword "type"
  prettySignatureEntry sig x (ElemEntry ctx ty) = return $
    !(prettyContext sig ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    annotate ContextVar (pretty x)
     <++>
    annotate Keyword ":"
     <++>
    !(prettyTypE sig (map fst $ tail ctx) ty 0)
  prettySignatureEntry sig x (LetElemEntry ctx e ty) = return $
    !(prettyContext sig ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    annotate ContextVar (pretty x)
     <++>
    annotate Keyword "≔"
     <++>
    !(prettyElem sig (map fst $ tail ctx) e 0)
     <++>
    annotate Keyword ":"
     <++>
    !(prettyTypE sig (map fst $ tail ctx) ty 0)
  prettySignatureEntry sig x (EqTyEntry ctx a b) = return $
    !(prettyContext sig ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    brackets' (annotate ContextVar (pretty x))
     <++>
    !(prettyTypE sig (map fst $ tail ctx) a 0)
     <++>
    annotate Keyword "="
     <++>
    !(prettyTypE sig (map fst $ tail ctx) b 0)
     <++>
    annotate Keyword "type"

  public export
  prettySignature' : SnocList VarName -> List (VarName, SignatureEntry) -> M (Doc Ann)
  prettySignature' sig [] = return ""
  prettySignature' sig ((x, e) :: es) = return $
    parens' !(prettySignatureEntry sig x e)
     <+>
    hardline
     <+>
    !(prettySignature' (sig :< x) es)

  public export
  prettySignature : SnocList VarName -> Signature -> M (Doc Ann)
  prettySignature sig sig' = prettySignature' sig (toList sig')

public export
renderDocAnsi : Doc AnsiStyle
             -> String
renderDocAnsi doc = renderString $ layoutPretty defaultLayoutOptions doc

toAnsiStyle : Ann -> AnsiStyle
toAnsiStyle Keyword = color Yellow
toAnsiStyle ContextVar = color BrightBlack
toAnsiStyle SignatureVar = color BrightBlack
toAnsiStyle Form = color Cyan
toAnsiStyle Elim = color Red
toAnsiStyle Intro = color Green

public export
renderDocTerm : Doc Ann
             -> String
renderDocTerm doc = renderDocAnsi (reAnnotate toAnsiStyle doc)

public export
renderDocNoAnn : Doc ann
              -> String
renderDocNoAnn doc = renderDocAnsi (unAnnotate doc)
