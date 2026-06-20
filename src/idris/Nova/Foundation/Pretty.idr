module Nova.Foundation.Pretty

import Data.String
import Data.SnocList

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Foundation.Syntax

public export
data Ann = Keyword | ContextVar | Form | Elim | Intro

public export
parens' : Doc Ann -> Doc Ann
parens' = enclose (annotate Keyword lparen) (annotate Keyword rparen)

public export
introParens' : Doc Ann -> Doc Ann
introParens' = enclose (annotate Intro lparen) (annotate Intro rparen)

Level : Type
Level = Nat

natToSubscript : Nat -> String
natToSubscript n = pack (map sub (unpack (show n)))
  where
    sub : Char -> Char
    sub '0' = '₀'; sub '1' = '₁'; sub '2' = '₂'
    sub '3' = '₃'; sub '4' = '₄'; sub '5' = '₅'
    sub '6' = '₆'; sub '7' = '₇'; sub '8' = '₈'
    sub '9' = '₉'; sub c = c

-- Precedences: 0 = outermost (λ, →, ⨯, ≡∈), 1 = ⨯ body, 2 = ≡ args,
--              3 = application spine, 4 = atoms
wrapTyp : Typ -> Level -> Doc Ann -> Doc Ann
wrapTyp UniverseTy _ doc = doc
wrapTyp NatTy _ doc = doc
wrapTyp ZeroTy _ doc = doc
wrapTyp OneTy _ doc = doc
wrapTyp (El _) lvl doc = if lvl > 3 then parens' doc else doc
wrapTyp (PiTy _ _) lvl doc = if lvl > 0 then parens' doc else doc
wrapTyp (SigmaTy _ _) lvl doc = if lvl > 1 then parens' doc else doc
wrapTyp (EqTy _ _ _) lvl doc = if lvl > 1 then parens' doc else doc
wrapTyp (SubstElim _ _) lvl doc = if lvl > 3 then parens' doc else doc

wrapElem : Elem -> Level -> Doc Ann -> Doc Ann
wrapElem NatTy _ doc = doc
wrapElem ZeroTy _ doc = doc
wrapElem OneTy _ doc = doc
wrapElem NatIntro0 _ doc = doc
wrapElem OneIntro _ doc = doc
wrapElem Refl _ doc = doc
wrapElem (CtxVar _) _ doc = doc
wrapElem (SigmaIntro _ _) _ doc = doc  -- always wrapped in introParens'
wrapElem (PiTy _ _) lvl doc = if lvl > 0 then parens' doc else doc
wrapElem (SigmaTy _ _) lvl doc = if lvl > 1 then parens' doc else doc
wrapElem (EqTy _ _ _) lvl doc = if lvl > 1 then parens' doc else doc
wrapElem (PiIntro _) lvl doc = if lvl > 0 then parens' doc else doc
wrapElem (PiElim _ _) lvl doc = if lvl > 3 then parens' doc else doc
wrapElem (SigmaElim1 _) lvl doc = if lvl > 3 then parens' doc else doc
wrapElem (SigmaElim2 _) lvl doc = if lvl > 3 then parens' doc else doc
wrapElem (NatIntro1 _) lvl doc = if lvl > 3 then parens' doc else doc
wrapElem (NatElim _ _ _ _) lvl doc = if lvl > 3 then parens' doc else doc
wrapElem (ZeroElim _) lvl doc = if lvl > 3 then parens' doc else doc
wrapElem (SubstElim _ _) lvl doc = if lvl > 3 then parens' doc else doc

mutual
  ||| depth = number of enclosing context binders (for de Bruijn index display)
  public export
  prettySubstContext : Nat -> SubstContext -> Doc Ann
  prettySubstContext _ Terminal = annotate Keyword "·"
  prettySubstContext _ Id = annotate Keyword "id"
  prettySubstContext _ Wk = annotate Keyword "↑"
  prettySubstContext depth (Chain s t) =
    prettySubstContext depth s <++> annotate Keyword "∘" <++> prettySubstContext depth t
  prettySubstContext depth (Ext s t) =
    parens' (prettySubstContext depth s <+> annotate Keyword "," <++> prettyElem depth t 0)

  public export
  prettyTyp' : Nat -> Typ -> Doc Ann
  prettyTyp' _ UniverseTy = annotate Form "𝕌"
  prettyTyp' _ NatTy = annotate Form "ℕ"
  prettyTyp' _ ZeroTy = annotate Form "𝟘"
  prettyTyp' _ OneTy = annotate Form "𝟙"
  prettyTyp' depth (El t) =
    annotate Elim "El" <++> prettyElem depth t 4
  prettyTyp' depth (PiTy a b) =
    prettyTyp depth a 3 <++> annotate Keyword "→" <++> prettyTyp (S depth) b 0
  prettyTyp' depth (SigmaTy a b) =
    prettyTyp depth a 2 <++> annotate Keyword "⨯" <++> prettyTyp (S depth) b 1
  prettyTyp' depth (EqTy t0 t1 a) =
    prettyElem depth t0 2 <++>
    annotate Form "≡" <++>
    prettyElem depth t1 2 <++>
    annotate Form "∈" <++>
    prettyTyp depth a 0
  prettyTyp' depth (SubstElim t sigma) =
    prettyTyp depth t 4 <+> parens' (prettySubstContext depth sigma)

  public export
  prettyTyp : Nat -> Typ -> Level -> Doc Ann
  prettyTyp depth tm lvl = wrapTyp tm lvl (prettyTyp' depth tm)

  public export
  prettyElem' : Nat -> Elem -> Doc Ann
  prettyElem' depth (SubstElim t sigma) =
    prettyElem depth t 4 <+> parens' (prettySubstContext depth sigma)
  prettyElem' depth (PiIntro f) =
    annotate Keyword "λ" <++> prettyElem (S depth) f 0
  prettyElem' depth (PiElim f e) =
    prettyElem depth f 3 <++> prettyElem depth e 4
  prettyElem' depth (SigmaElim1 t) =
    prettyElem depth t 3 <++> annotate Elim ".π₁"
  prettyElem' depth (SigmaElim2 t) =
    prettyElem depth t 3 <++> annotate Elim ".π₂"
  prettyElem' depth (SigmaIntro a b) =
    introParens' (prettyElem depth a 0 <+> annotate Intro "," <++> prettyElem depth b 0)
  prettyElem' depth (PiTy a b) =
    prettyElem depth a 3 <++> annotate Keyword "→" <++> prettyElem (S depth) b 0
  prettyElem' depth (SigmaTy a b) =
    prettyElem depth a 2 <++> annotate Keyword "⨯" <++> prettyElem (S depth) b 1
  prettyElem' _ NatTy = annotate Form "ℕ"
  prettyElem' _ ZeroTy = annotate Form "𝟘"
  prettyElem' _ OneTy = annotate Form "𝟙"
  prettyElem' depth (EqTy t0 t1 a) =
    prettyElem depth t0 2 <++>
    annotate Form "≡" <++>
    prettyElem depth t1 2 <++>
    annotate Form "∈" <++>
    prettyElem depth a 0
  prettyElem' _ OneIntro = annotate Intro "()"
  prettyElem' _ NatIntro0 = annotate Intro "Z"
  prettyElem' depth (NatIntro1 t) =
    annotate Intro "S" <++> prettyElem depth t 4
  prettyElem' depth (NatElim motive z s t) =
    annotate Elim "ℕ-elim"
      <++>
    parens' (annotate Keyword "☐" <+> annotate Keyword "." <++> prettyTyp (S depth) motive 0)
      <++>
    prettyElem depth z 4
      <++>
    parens' (    annotate Keyword "☐"
             <+> annotate Keyword "."
             <+> annotate Keyword "☐"
             <+> annotate Keyword "."
             <++> prettyElem (S (S depth)) s 0)
      <++>
    prettyElem depth t 4
  prettyElem' depth (ZeroElim t) =
    annotate Elim "𝟘-elim" <++> prettyElem depth t 4
  prettyElem' _ (CtxVar i) =
    annotate ContextVar (pretty $ "☐" ++ natToSubscript i)
  prettyElem' _ Refl = annotate Intro "Refl"

  public export
  prettyElem : Nat -> Elem -> Level -> Doc Ann
  prettyElem depth tm lvl = wrapElem tm lvl (prettyElem' depth tm)

||| Pretty-print a typing context as a space-separated telescope of types.
||| Each type is printed in the sub-context formed by all preceding types.
public export
prettyCtx : Ctx -> Doc Ann
prettyCtx ctx = go 0 (toList ctx)
  where
    go : Nat -> List Typ -> Doc Ann
    go _ [] = annotate Form "ε"
    go depth (ty :: rest) = prettyTyp depth ty 0 <++> go (S depth) rest

||| Δ(σ) — telescope printed with increasing depth under each binder.
public export
prettyTel : Nat -> Tel -> Doc Ann
prettyTel _ [] = annotate Form "ε"
prettyTel depth (ty :: rest) = prettyTyp depth ty 0 <++> prettyTel (S depth) rest

||| ē — element list, all elements printed at the same depth.
public export
prettyElemList : Nat -> ElemList -> Doc Ann
prettyElemList _ [] = annotate Keyword "·"
prettyElemList depth (e :: rest) = prettyElem depth e 0 <++> prettyElemList depth rest

toAnsiStyle : Ann -> AnsiStyle
toAnsiStyle Keyword    = color Yellow
toAnsiStyle ContextVar = color BrightBlack
toAnsiStyle Form       = color Cyan
toAnsiStyle Elim       = color Red
toAnsiStyle Intro      = color Green

public export
renderDocTerm : Doc Ann -> String
renderDocTerm doc =
  renderString $ layoutPretty defaultLayoutOptions (reAnnotate toAnsiStyle doc)

public export
renderDocNoAnn : Doc ann -> String
renderDocNoAnn doc =
  renderString $ layoutPretty defaultLayoutOptions (unAnnotate doc)
