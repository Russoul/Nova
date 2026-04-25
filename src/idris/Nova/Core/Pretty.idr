module Nova.Core.Pretty

import Data.Fin
import Data.AVL
import Data.String
import Data.Util

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Control.Monad.Reader
import Nova.Control.Monad.Id

import Nova.Core.Language
import Nova.Core.Shrinking
import Nova.Core.Substitution
import Nova.Core.Evaluation

public export
record PrettyCfg where
  constructor MkPrettyCfg
  showImplicitArguments : Bool

public export
prettyCfgDefault : PrettyCfg
prettyCfgDefault = MkPrettyCfg True

PrettyM = Reader PrettyCfg

public export
data Ann = Keyword | ContextVar | SignatureVar | Form | Elim | Intro

public export
parens' : Doc Ann -> Doc Ann
parens' = enclose (annotate Keyword lparen) (annotate Keyword rparen)

public export
introParens' : Doc Ann -> Doc Ann
introParens' = enclose (annotate Intro lparen) (annotate Intro rparen)

public export
introBraces' : Doc Ann -> Doc Ann
introBraces' = enclose (annotate Intro lbrace) (annotate Intro rbrace)

public export
elimBraces' : Doc Ann -> Doc Ann
elimBraces' = enclose (annotate Elim lbrace) (annotate Elim rbrace)

public export
brackets' : Doc Ann -> Doc Ann
brackets' = enclose (annotate Keyword lbracket) (annotate Keyword rbracket)

Level = Fin 5

wrapTyp : Typ -> Level -> Doc Ann -> PrettyM (Doc Ann)
wrapTyp (PiTy x dom cod) lvl doc = Reader.do
  case shrink cod 1 0 of
    Nothing =>
      case lvl <= 0 of
        True => pure doc
        False => pure (parens' doc)
    Just _ =>
      case lvl <= 2 of
        True => pure doc
        False => pure (parens' doc)
wrapTyp (ImplicitPiTy x dom cod) lvl doc =
  case lvl <= 0 of
    True => pure doc
    False => pure (parens' doc)
wrapTyp (SigmaTy x dom cod) lvl doc =
  case shrink cod 1 0 of
    Nothing =>
      case lvl <= 0 of
        True => pure doc
        False => pure (parens' doc)
    Just _ =>
      case lvl <= 1 of
        True => pure doc
        False => pure (parens' doc)
wrapTyp NatTy lvl doc =
  case lvl <= 4 of
    True => pure doc
    False => pure (parens' doc)
wrapTyp ZeroTy lvl doc =
  case lvl <= 4 of
    True => pure doc
    False => pure (parens' doc)
wrapTyp OneTy lvl doc =
  case lvl <= 4 of
    True => pure doc
    False => pure (parens' doc)
wrapTyp UniverseTy lvl doc =
  case lvl <= 4 of
    True => pure doc
    False => pure (parens' doc)
wrapTyp tm@(ContextSubstElim {}) lvl doc = assert_total $ idris_crash "wrapTyp(ContextSubstElim)"
wrapTyp tm@(SignatureSubstElim {}) lvl doc = assert_total $ idris_crash "wrapTyp(SignatureSubstElim)"
wrapTyp (OmegaVarElim {}) lvl doc =
  case lvl <= 3 of
    True => pure doc
    False => pure (parens' doc)
wrapTyp (TyEqTy {}) lvl doc =
  case lvl <= 1 of
    True => pure doc
    False => pure (parens' doc)
wrapTyp (ElEqTy {}) lvl doc =
  case lvl <= 1 of
    True => pure doc
    False => pure (parens' doc)
wrapTyp (El {}) lvl doc =
  case lvl <= 3 of
    True => pure doc
    False => pure (parens' doc)
wrapTyp (SignatureVarElim {}) lvl doc =
  case lvl <= 3 of
    True => pure doc
    False => pure (parens' doc)

wrapElem : Elem -> Level -> Doc Ann -> PrettyM (Doc Ann)
wrapElem (PiTy x dom cod) lvl doc =
  case shrink cod 1 0 of
    Nothing =>
      case lvl <= 0 of
        True => pure doc
        False => pure (parens' doc)
    Just _ =>
      case lvl <= 2 of
        True => pure doc
        False => pure (parens' doc)
wrapElem (ImplicitPiTy x dom cod) lvl doc =
  case lvl <= 0 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (SigmaTy x dom cod) lvl doc =
  case shrink cod 1 0 of
    Nothing =>
      case lvl <= 0 of
        True => pure doc
        False => pure (parens' doc)
    Just _ =>
      case lvl <= 1 of
        True => pure doc
        False => pure (parens' doc)
wrapElem (PiVal {}) lvl doc =
  case lvl <= 0 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (ImplicitPiVal {}) lvl doc =
  case lvl <= 0 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (SigmaVal {}) lvl doc =
  case lvl <= 4 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (PiElim {}) lvl doc =
  case lvl <= 3 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (ImplicitPiElim {}) lvl doc =
  case lvl <= 3 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (SigmaElim1 {}) lvl doc =
  case lvl <= 3 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (SigmaElim2 {}) lvl doc =
  case lvl <= 3 of
    True => pure doc
    False => pure (parens' doc)
wrapElem NatVal0 lvl doc =
  case lvl <= 4 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (NatVal1 x) lvl doc =
  case lvl <= 3 of
    True => pure doc
    False => pure (parens' doc)
wrapElem NatTy lvl doc =
  case lvl <= 4 of
    True => pure doc
    False => pure (parens' doc)
wrapElem ZeroTy lvl doc =
  case lvl <= 4 of
    True => pure doc
    False => pure (parens' doc)
wrapElem OneTy lvl doc =
  case lvl <= 4 of
    True => pure doc
    False => pure (parens' doc)
wrapElem OneVal lvl doc =
  case lvl <= 4 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (NatElim str x y str1 str2 z w) lvl doc =
  case lvl <= 3 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (ZeroElim _ _) lvl doc =
  case lvl <= 3 of
    True => pure doc
    False => pure (parens' doc)
wrapElem tm@(ContextSubstElim {}) lvl doc = assert_total $ idris_crash "wrapElem(ContextSubstElim)"
wrapElem tm@(SignatureSubstElim {}) lvl doc = assert_total $ idris_crash "wrapElem(SignatureSubstElim)"
wrapElem (ContextVarElim {}) lvl doc =
  case lvl <= 4 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (SignatureVarElim {}) lvl doc =
  case lvl <= 3 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (OmegaVarElim {}) lvl doc =
  case lvl <= 3 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (TyEqTy {}) lvl doc =
  case lvl <= 1 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (ElEqTy {}) lvl doc =
  case lvl <= 1 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (TyEqVal {}) lvl doc =
  case lvl <= 4 of
    True => pure doc
    False => pure (parens' doc)
wrapElem (ElEqVal {}) lvl doc =
  case lvl <= 4 of
    True => pure doc
    False => pure (parens' doc)

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
localise : SnocList VarName -> Nat -> PrettyM (Maybe (VarName, Nat))
localise [<] idx = assert_total $ idris_crash "Critical error in 'localise'"
localise (xs :< x) Z = Reader.pure (Just (x, 0))
localise (xs :< x) (S k) = Reader.do
  Just (name, idx) <- localise xs k
    | Nothing => Reader.pure Nothing
  case name == x of
    True => Reader.pure (Just (name, S idx))
    False => Reader.pure (Just (name, idx))

public export
prettySignatureVar : Signature -> Nat -> PrettyM (Doc Ann)
prettySignatureVar sig i = Reader.do
  --
  case !(localise (map fst sig) i) of
    Just ok =>
      case ok of
        (n, 0) => pure (annotate SignatureVar (pretty n))
        (n, k) => pure (annotate SignatureVar (pretty n <+> "{" <+> pretty k <+> "}"))
    Nothing =>
      pure (annotate Elim (pretty $ "χ" ++ natToSuperscript i ++ " <broken index #\{show (length sig)}>"))

public export
prettyContextVar : SnocList VarName -> Nat -> PrettyM (Doc Ann)
prettyContextVar ctx i = Reader.do
  case !(localise ctx i) of
    Just ok =>
      case ok of
        (n, 0) => pure (annotate SignatureVar (pretty n))
        (n, k) => pure (annotate SignatureVar (pretty n <+> "{" <+> pretty k <+> "}"))
    Nothing =>
      pure (annotate Elim (pretty $ "x" ++ natToSuperscript i ++ " <broken index #\{show (length ctx)}>"))

mutual
  public export
  prettySubstContextNu' : Signature -> Omega -> SnocList VarName -> SubstContextNF -> PrettyM (Doc Ann)
  prettySubstContextNu' sig omega ctx (WkN k) = pure (pretty "↑\{natToSuperscript k}")
  prettySubstContextNu' sig omega ctx (Ext sigma t) = pure $ parens' $
    !(prettySubstContext' sig omega ctx sigma)
     <+>
    annotate Keyword ","
     <++>
    !(prettyElem sig omega ctx t 0)
  prettySubstContextNu' sig omega ctx Terminal = pure "·"

  public export
  prettySubstContext' : Signature -> Omega -> SnocList VarName -> SubstContext -> PrettyM (Doc Ann)
  prettySubstContext' sig omega ctx sigma = prettySubstContextNu' sig omega ctx (eval sigma)

  public export
  prettySubstContext : Signature -> Omega -> SnocList VarName -> SubstContext -> PrettyM (Doc Ann)
  prettySubstContext sig omega ctx sigma = prettySubstContext' sig omega ctx sigma

  public export
  prettyTyp' : Signature
            -> Omega
            -> SnocList VarName
            -> Typ
            -> PrettyM (Doc Ann)
  prettyTyp' sig omega ctx (El a) = Reader.pure $
    annotate Elim "El"
      <++>
    !(prettyElem sig omega ctx a 4)
  prettyTyp' sig omega ctx (PiTy x dom cod) = Reader.do
    case shrink cod 1 0 of
      Nothing => Reader.do
        pure $
          annotate Intro lparen
           <+>
          annotate ContextVar (pretty x)
           <++>
          annotate Keyword ":"
           <++>
          !(prettyTyp sig omega ctx dom 0)
           <+>
          annotate Intro rparen
           <++>
          annotate Keyword "→"
           <++>
          !(prettyTyp sig omega (ctx :< x) cod 0)
      Just cod => Reader.do
        pure $
          !(prettyTyp sig omega ctx dom 3)
           <++>
          annotate Keyword "→"
           <++>
          !(prettyTyp sig omega ctx cod 2)
  prettyTyp' sig omega ctx (ImplicitPiTy x dom cod) = Reader.do
    pure $
      annotate Intro lbrace
       <+>
      annotate ContextVar (pretty x)
       <++>
      annotate Keyword ":"
       <++>
      !(prettyTyp sig omega ctx dom 0)
       <+>
      annotate Intro rbrace
       <++>
      annotate Keyword "→"
       <++>
      !(prettyTyp sig omega (ctx :< x) cod 0)
  prettyTyp' sig omega ctx (SigmaTy x dom cod) = Reader.do
    case shrink cod 1 0 of
      Nothing => Reader.do
        pure $
          annotate Intro lparen
           <+>
          annotate ContextVar (pretty x)
           <++>
          annotate Keyword ":"
           <++>
          !(prettyTyp sig omega ctx dom 0)
           <+>
          annotate Intro rparen
           <++>
          annotate Keyword "⨯"
           <++>
          !(prettyTyp sig omega (ctx :< x) cod 0)
      Just cod => Reader.do
        pure $
          !(prettyTyp sig omega ctx dom 4)
           <++>
          annotate Keyword "⨯"
           <++>
          !(prettyTyp sig omega ctx cod 4)
  prettyTyp' sig omega ctx NatTy =
    pure $ annotate Form "ℕ"
  prettyTyp' sig omega ctx ZeroTy =
    pure $ annotate Form "𝟘"
  prettyTyp' sig omega ctx OneTy =
    pure $ annotate Form "𝟙"
  prettyTyp' sig omega ctx UniverseTy =
    pure $ annotate Form "𝕌"
  prettyTyp' sig omega ctx tm@(ContextSubstElim {}) = assert_total $ idris_crash "prettyTyp'(ContextSubstElim)"
  prettyTyp' sig omega ctx tm@(SignatureSubstElim {}) = assert_total $ idris_crash "prettyTyp'(SignatureSubstElim)"
  prettyTyp' sig omega ctx (OmegaVarElim k sigma) = Reader.do
    let x = annotate Elim (pretty k)
    pure $
      x
       <+>
      !(case eval sigma of
        Terminal => pure ""
        nf => Reader.do pure $ parens' !(prettySubstContextNu' sig omega ctx nf)
      )
  prettyTyp' sig omega ctx (TyEqTy l r) = pure $
    !(prettyTyp sig omega ctx l 3)
     <++>
    annotate Form "≡"
     <++>
    !(prettyTyp sig omega ctx r 3)
  prettyTyp' sig omega ctx (ElEqTy l r ty) = pure $
    !(prettyElem sig omega ctx l 3)
     <++>
    annotate Form "≡"
     <++>
    !(prettyElem sig omega ctx r 3)
     <++>
    annotate Form "∈"
     <++>
    !(prettyTyp sig omega ctx ty 0)
  prettyTyp' sig omega ctx (SignatureVarElim k sigma) = Reader.do
    x <- prettySignatureVar sig k
    pure $
      x
       <+>
      !(case eval sigma of
        Terminal => pure ""
        nf => Reader.do pure $ parens' !(prettySubstContextNu' sig omega ctx nf)
      )

  public export
  prettyTyp : Signature
           -> Omega
           -> SnocList VarName
           -> Typ
           -> Level
           -> PrettyM (Doc Ann)
  prettyTyp sig omega ctx tm lvl = Reader.do
    let tm = openEval sig omega tm
    wrapTyp tm lvl !(prettyTyp' sig omega ctx tm)

  public export
  prettyTypDefault : Signature
                  -> Omega
                  -> SnocList VarName
                  -> Typ
                  -> Level
                  -> Doc Ann
  prettyTypDefault sig omega ctx tm lvl = prettyTyp sig omega ctx tm lvl prettyCfgDefault

  public export
  prettyElem' : Signature
             -> Omega
             -> SnocList VarName
             -> Elem
             -> PrettyM (Doc Ann)
  prettyElem' sig omega ctx (PiTy x dom cod) = Reader.do
    case shrink cod 1 0 of
      Nothing => Reader.do
        pure $
          annotate Intro lparen
           <+>
          annotate ContextVar (pretty x)
           <++>
          annotate Keyword ":"
           <++>
          !(prettyElem sig omega ctx dom 0)
           <+>
          annotate Intro rparen
           <++>
          annotate Keyword "→"
           <++>
          !(prettyElem sig omega (ctx :< x) cod 0)
      Just cod => Reader.do
        pure $
          !(prettyElem sig omega ctx dom 3)
           <++>
          annotate Keyword "→"
           <++>
          !(prettyElem sig omega ctx cod 2)
  prettyElem' sig omega ctx (ImplicitPiTy x dom cod) = Reader.do
    pure $
      annotate Intro lbrace
       <+>
      annotate ContextVar (pretty x)
       <++>
      annotate Keyword ":"
       <++>
      !(prettyElem sig omega ctx dom 0)
       <+>
      annotate Intro rbrace
       <++>
      annotate Keyword "→"
       <++>
      !(prettyElem sig omega (ctx :< x) cod 0)
  prettyElem' sig omega ctx (SigmaTy x dom cod) = Reader.do
    case shrink cod 1 0 of
      Nothing => Reader.do
        pure $
          annotate Intro lparen
           <+>
          annotate ContextVar (pretty x)
           <++>
          annotate Keyword ":"
           <++>
          !(prettyElem sig omega ctx dom 0)
           <+>
          annotate Intro rparen
           <++>
          annotate Keyword "⨯"
           <++>
          !(prettyElem sig omega (ctx :< x) cod 0)
      Just cod => Reader.do
        pure $
          !(prettyElem sig omega ctx dom 4)
           <++>
          annotate Keyword "⨯"
           <++>
          !(prettyElem sig omega ctx cod 4)
  prettyElem' sig omega ctx (PiVal x _ _ f) =
    pure $
      annotate ContextVar (pretty x)
       <++>
      annotate Intro "↦"
       <++>
      !(prettyElem sig omega (ctx :< x) f 0)
  prettyElem' sig omega ctx (ImplicitPiVal x _ _ f) =
    pure $
      introBraces' (annotate ContextVar (pretty x))
       <++>
      annotate Intro "↦"
       <++>
      !(prettyElem sig omega (ctx :< x) f 0)
  prettyElem' sig omega ctx (SigmaVal _ _ _ a b) =
    pure $ introParens' $
      !(prettyElem sig omega ctx a 0)
       <+>
      annotate Intro ","
       <++>
      !(prettyElem sig omega ctx b 0)
  prettyElem' sig omega ctx (PiElim f x a b e) =
    pure $
      !(prettyElem sig omega ctx f 3)
       <++>
      !(prettyElem sig omega ctx e 4)
  prettyElem' sig omega ctx (ImplicitPiElim f x a b e) = Reader.do
    prettyF <- prettyElem sig omega ctx f 3
    case !(showImplicitArguments <$> read) of
      True => pure $ prettyF <++> elimBraces' !(prettyElem sig omega ctx e 0)
      False => pure prettyF
  prettyElem' sig omega ctx (SigmaElim1 f x a b) =
    pure $
      !(prettyElem sig omega ctx f 3)
       <++>
      annotate Elim ".π₁"
  prettyElem' sig omega ctx (SigmaElim2 f x a b) =
    pure $
      !(prettyElem sig omega ctx f 3)
       <++>
      annotate Elim ".π₂"
  prettyElem' sig omega ctx NatVal0 =
    pure $ annotate Intro "Z"
  prettyElem' sig omega ctx (NatVal1 e) = pure $
    annotate Intro "S"
      <++>
    !(prettyElem sig omega ctx e 4)
  prettyElem' sig omega ctx NatTy =
    pure $ annotate Form "ℕ"
  prettyElem' sig omega ctx ZeroTy =
    pure $ annotate Form "𝟘"
  prettyElem' sig omega ctx OneTy =
    pure $ annotate Form "𝟙"
  prettyElem' sig omega ctx OneVal =
    pure $ annotate Intro "()"
  prettyElem' sig omega ctx (ZeroElim _ t) = Reader.do
    pure $
      annotate Elim "𝟘-elim"
       <++>
      !(prettyElem sig omega ctx t 4)
  prettyElem' sig omega ctx (NatElim x schema z y h s t) = Reader.do
    pure $
      annotate Elim "ℕ-elim"
       <++>
      parens' (annotate ContextVar (pretty x) <+> annotate Keyword "." <++> !(prettyTyp sig omega (ctx :< x) schema 0))
       <++>
      !(prettyElem sig omega ctx z 4)
       <++>
      parens' (annotate ContextVar (pretty y)
                <+>
               annotate Keyword "."
                <+>
               annotate ContextVar (pretty h)
                <+>
               annotate Keyword "."
                <++>
               !(prettyElem sig omega (ctx :< y :< h) s 0)
              )
       <++>
      !(prettyElem sig omega ctx t 4)
  prettyElem' sig omega ctx tm@(ContextSubstElim {}) = assert_total $ idris_crash "prettyElem'(ContextSubstElim)"
  prettyElem' sig omega ctx tm@(SignatureSubstElim {}) = assert_total $ idris_crash "prettyElem'(SignatureSubstElim)"
  prettyElem' sig omega ctx (ContextVarElim k) =
    prettyContextVar ctx k
  prettyElem' sig omega ctx (SignatureVarElim k sigma) = Reader.do
    x <- prettySignatureVar sig k
    pure $
      x
       <+>
      !(case eval sigma of
        Terminal => pure ""
        nf => Reader.do pure $ parens' !(prettySubstContextNu' sig omega ctx nf)
      )
  prettyElem' sig omega ctx (OmegaVarElim k sigma) = Reader.do
    let x = annotate Elim (pretty k)
    pure $
      x
       <+>
      !(case eval sigma of
        Terminal => pure ""
        nf => Reader.do pure $ parens' !(prettySubstContextNu' sig omega ctx nf)
      )
  prettyElem' sig omega ctx (TyEqTy l r) = pure $
    !(prettyElem sig omega ctx l 3)
     <++>
    annotate Form "≡"
     <++>
    !(prettyElem sig omega ctx r 3)
  prettyElem' sig omega ctx (ElEqTy l r ty) = pure $
    !(prettyElem sig omega ctx l 3)
     <++>
    annotate Form "≡"
     <++>
    !(prettyElem sig omega ctx r 3)
     <++>
    annotate Form "∈"
     <++>
    !(prettyElem sig omega ctx ty 0)
  prettyElem' sig omega ctx (TyEqVal _) =
    pure $ annotate Intro "Refl"
  prettyElem' sig omega ctx (ElEqVal _ _) =
    pure $ annotate Intro "Refl"

  public export
  prettyElem : Signature
            -> Omega
            -> SnocList VarName
            -> Elem
            -> Level
            -> PrettyM (Doc Ann)
  prettyElem sig omega ctx tm lvl = Reader.do
    let tm = openEval sig omega tm
    wrapElem tm lvl !(prettyElem' sig omega ctx tm)

  public export
  prettyTelescope : Signature
                 -> Omega
                 -> SnocList VarName
                 -> List (VarName, Typ)
                 -> PrettyM (Doc Ann)
  prettyTelescope sig omega ctx [] = pure ""
  prettyTelescope sig omega ctx ((x, ty) :: tyes) = pure $
    lparen
     <+>
    annotate ContextVar (pretty x)
     <++>
    annotate Keyword ":"
     <++>
    !(prettyTyp sig omega ctx ty 0)
     <+>
    rparen
     <++>
    !(prettyTelescope sig omega (ctx :< x) tyes)

  public export
  prettyContext : Signature
               -> Omega
               -> Context
               -> PrettyM (Doc Ann)
  prettyContext sig omega ctx = prettyTelescope sig omega [<] (cast ctx)

  public export
  prettySignatureEntry : Signature -> Omega -> VarName -> SignatureEntry -> PrettyM (Doc Ann)
   -- Γ ⊦ χ : A
   -- Γ ⊦ χ ≔ e : A
   -- Γ ⊦ χ type
   -- Γ ⊦ χ ≔ A type
  prettySignatureEntry sig omega x (ElemEntry ctx ty) = pure $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    annotate ContextVar (pretty x)
     <++>
    annotate Keyword ":"
     <++>
    !(prettyTyp sig omega (map fst ctx) ty 0)
  prettySignatureEntry sig omega x (LetElemEntry ctx e ty) = pure $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    annotate ContextVar (pretty x)
     <++>
    annotate Keyword "≔"
     <++>
    !(prettyElem sig omega (map fst ctx) e 0)
     <++>
    annotate Keyword ":"
     <++>
    !(prettyTyp sig omega (map fst ctx) ty 0)
  prettySignatureEntry sig omega x (TypeEntry ctx) = pure $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    annotate ContextVar (pretty x)
     <++>
    annotate Keyword "type"
  prettySignatureEntry sig omega x (LetTypeEntry ctx e) = pure $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    annotate ContextVar (pretty x)
     <++>
    annotate Keyword "≔"
     <++>
    !(prettyTyp sig omega (map fst ctx) e 0)
     <++>
    annotate Keyword "type"

  public export
  prettyConstraintEntry : Signature -> Omega -> ConstraintEntry -> PrettyM (Doc Ann)
  prettyConstraintEntry sig omega (TypeConstraint ctx a b) = Reader.do
   pure $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    !(prettyTyp sig omega (map fst ctx) a 0)
     <++>
    annotate Keyword "="
     <++>
    !(prettyTyp sig omega (map fst ctx) b 0)
     <++>
    annotate Keyword "type"
  prettyConstraintEntry sig omega (ElemConstraint ctx a b ty) = Reader.do
   pure $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    !(prettyElem sig omega (map fst ctx) a 0)
     <++>
    annotate Keyword "="
     <++>
    !(prettyElem sig omega (map fst ctx) b 0)
     <++>
    annotate Keyword ":"
     <++>
    !(prettyTyp sig omega (map fst ctx) ty 0)
  prettyConstraintEntry sig omega (SubstContextConstraint sigma tau source target) = Reader.do
   pure $
    !(prettySubstContext sig omega [<] sigma)
     <++>
    annotate Keyword "="
     <++>
    !(prettySubstContext sig omega [<] tau)
     <++>
    annotate Keyword ":"
     <++>
    !(prettyContext sig omega source)
     <++>
    annotate Keyword "⇒"
     <++>
    !(prettyContext sig omega target)

  public export
  prettyConstraints : Signature -> Omega -> Constraints -> PrettyM (Doc Ann)
  prettyConstraints sig omega cs =
    pure $ vsep !(Reader.List.for (cast cs) (prettyConstraintEntry sig omega))

  public export
  prettySignature' : Signature -> Omega -> List (VarName, SignatureEntry) -> PrettyM (Doc Ann)
  prettySignature' sig omega [] = pure ""
  prettySignature' sig omega ((x, e) :: es) = pure $
    parens' !(prettySignatureEntry sig omega x e)
     <+>
    hardline
     <+>
    !(prettySignature' (sig :< (x, e)) omega es)

  public export
  prettySignature : Signature -> Omega -> Signature -> PrettyM (Doc Ann)
  prettySignature sig omega sig' = prettySignature' sig omega (toList sig')

  public export
  prettySignatureDefault : Signature -> Omega -> Signature -> Doc Ann
  prettySignatureDefault sig omega sig' = prettySignature sig omega sig' prettyCfgDefault

  public export
  prettyMetaKind : MetaKind -> Doc Ann
  prettyMetaKind NoSolve = "NoSolve"
  prettyMetaKind SolveByUnification = "SolveByUnification"
  prettyMetaKind SolveByElaboration = "SolveByElaboration"

  public export
  prettyOmegaEntry : Signature -> Omega -> OmegaName -> OmegaEntry -> PrettyM (Doc Ann)
  prettyOmegaEntry sig omega n (MetaType ctx k) = Reader.do
   pure $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    pretty n
     <++>
    annotate Keyword "type"
     <++>
    parens' (prettyMetaKind k)
  prettyOmegaEntry sig omega n (LetType ctx rhs) = Reader.do
   pure $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    pretty n
     <++>
    annotate Keyword "≔"
     <++>
    !(prettyTyp sig omega (map fst ctx) rhs 0)
     <++>
    annotate Keyword "type"
  prettyOmegaEntry sig omega n (MetaElem ctx ty k) = Reader.do
   pure $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    pretty n
     <++>
    annotate Keyword ":"
     <++>
    !(prettyTyp sig omega (map fst ctx) ty 0)
     <++>
    parens' (prettyMetaKind k)
  prettyOmegaEntry sig omega n (LetElem ctx rhs ty) = Reader.do
   pure $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    pretty n
     <++>
    annotate Keyword "≔"
     <++>
    !(prettyElem sig omega (map fst ctx) rhs 0)
     <++>
    annotate Keyword ":"
     <++>
    !(prettyTyp sig omega (map fst ctx) ty 0)
  prettyOmegaEntry sig omega n (TypeConstraint ctx a b) = Reader.do
   pure $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    !(prettyTyp sig omega (map fst ctx) a 0)
     <++>
    annotate Keyword "="
     <++>
    !(prettyTyp sig omega (map fst ctx) b 0)
     <++>
    annotate Keyword "type"
  prettyOmegaEntry sig omega n (ElemConstraint ctx a b ty) = Reader.do
   pure $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    !(prettyElem sig omega (map fst ctx) a 0)
     <++>
    annotate Keyword "="
     <++>
    !(prettyElem sig omega (map fst ctx) b 0)
     <++>
    annotate Keyword ":"
     <++>
    !(prettyTyp sig omega (map fst ctx) ty 0)
  prettyOmegaEntry sig omega n (SubstContextConstraint sigma tau source target) = Reader.do
   pure $
    !(prettySubstContext sig omega [<] sigma)
     <++>
    annotate Keyword "="
     <++>
    !(prettySubstContext sig omega [<] tau)
     <++>
    annotate Keyword ":"
     <++>
    !(prettyContext sig omega source)
     <++>
    annotate Keyword "⇒"
     <++>
    !(prettyContext sig omega target)

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

public export
prettyOmega' : Signature -> Omega -> List (VarName, OmegaEntry) -> PrettyM (Doc Ann)
prettyOmega' sig omega [] = pure ""
prettyOmega' sig omega ((x, e) :: es) = pure $
  parens' !(prettyOmegaEntry sig omega x e)
   <+>
  hardline
   <+>
  !(prettyOmega' sig omega es)

public export
prettyOmega : Signature -> Omega -> PrettyM (Doc Ann)
prettyOmega sig omega = prettyOmega' sig omega (List.inorder omega)

public export
prettyOmegaDefault : Signature -> Omega -> Doc Ann
prettyOmegaDefault sig omega = prettyOmega sig omega prettyCfgDefault
