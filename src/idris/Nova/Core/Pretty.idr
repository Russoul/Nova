module Nova.Core.Pretty

import Data.Fin
import Data.AVL
import Data.String
import Data.Util

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Shrinking
import Nova.Core.Substitution
import Nova.Core.Evaluation

-- (x : A{≥0}) → A{≥0}
-- (x : A{≥0}) ⨯ A{≥0}
-- e{≥3} ≡ e{≥3} ∈ e{≥0}

-- x ↦ e{≥0}
-- (e{≥0}, e{≥0})
-- S e{≥4}

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

wrapTyp : Typ -> Level -> Doc Ann -> M (Doc Ann)
wrapTyp (PiTy x dom cod) lvl doc =
  case !(shrink cod 1 0) of
    Nothing =>
      case lvl <= 0 of
        True => return doc
        False => return (parens' doc)
    Just _ =>
      case lvl <= 2 of
        True => return doc
        False => return (parens' doc)
wrapTyp (ImplicitPiTy x dom cod) lvl doc =
  case lvl <= 0 of
    True => return doc
    False => return (parens' doc)
wrapTyp (SigmaTy x dom cod) lvl doc =
  case !(shrink cod 1 0) of
    Nothing =>
      case lvl <= 0 of
        True => return doc
        False => return (parens' doc)
    Just _ =>
      case lvl <= 1 of
        True => return doc
        False => return (parens' doc)
wrapTyp NatTy lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapTyp ZeroTy lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapTyp OneTy lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapTyp UniverseTy lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapTyp tm@(ContextSubstElim {}) lvl doc = assert_total $ idris_crash "wrapTyp(ContextSubstElim)"
wrapTyp tm@(SignatureSubstElim {}) lvl doc = assert_total $ idris_crash "wrapTyp(SignatureSubstElim)"
wrapTyp (OmegaVarElim {}) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapTyp (TyEqTy {}) lvl doc =
  case lvl <= 1 of
    True => return doc
    False => return (parens' doc)
wrapTyp (ElEqTy {}) lvl doc =
  case lvl <= 1 of
    True => return doc
    False => return (parens' doc)
wrapTyp (El {}) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapTyp (SignatureVarElim {}) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)

wrapElem : Elem -> Level -> Doc Ann -> M (Doc Ann)
wrapElem (PiTy x dom cod) lvl doc =
  case !(shrink cod 1 0) of
    Nothing =>
      case lvl <= 0 of
        True => return doc
        False => return (parens' doc)
    Just _ =>
      case lvl <= 2 of
        True => return doc
        False => return (parens' doc)
wrapElem (ImplicitPiTy x dom cod) lvl doc =
  case lvl <= 0 of
    True => return doc
    False => return (parens' doc)
wrapElem (SigmaTy x dom cod) lvl doc =
  case !(shrink cod 1 0) of
    Nothing =>
      case lvl <= 0 of
        True => return doc
        False => return (parens' doc)
    Just _ =>
      case lvl <= 1 of
        True => return doc
        False => return (parens' doc)
wrapElem (PiVal {}) lvl doc =
  case lvl <= 0 of
    True => return doc
    False => return (parens' doc)
wrapElem (ImplicitPiVal {}) lvl doc =
  case lvl <= 0 of
    True => return doc
    False => return (parens' doc)
wrapElem (SigmaVal {}) lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapElem (PiElim {}) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapElem (ImplicitPiElim {}) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapElem (SigmaElim1 {}) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapElem (SigmaElim2 {}) lvl doc =
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
wrapElem ZeroTy lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapElem OneTy lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapElem OneVal lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapElem (NatElim str x y str1 str2 z w) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapElem (ZeroElim _ _) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapElem tm@(ContextSubstElim {}) lvl doc = assert_total $ idris_crash "wrapElem(ContextSubstElim)"
wrapElem tm@(SignatureSubstElim {}) lvl doc = assert_total $ idris_crash "wrapElem(SignatureSubstElim)"
wrapElem (ContextVarElim {}) lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapElem (SignatureVarElim {}) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapElem (OmegaVarElim {}) lvl doc =
  case lvl <= 3 of
    True => return doc
    False => return (parens' doc)
wrapElem (TyEqTy {}) lvl doc =
  case lvl <= 1 of
    True => return doc
    False => return (parens' doc)
wrapElem (ElEqTy {}) lvl doc =
  case lvl <= 1 of
    True => return doc
    False => return (parens' doc)
wrapElem (TyEqVal {}) lvl doc =
  case lvl <= 4 of
    True => return doc
    False => return (parens' doc)
wrapElem (ElEqVal {}) lvl doc =
  case lvl <= 4 of
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
localise [<] idx = criticalError "Critical error in 'localise'"
localise (xs :< x) Z = return (x, 0)
localise (xs :< x) (S k) = M.do
  (name, idx) <- localise xs k
  case name == x of
    True => return (name, S idx)
    False => return (name, idx)

public export
prettySignatureVar : Signature -> Nat -> M (Doc Ann)
prettySignatureVar sig i = M.do
  --
  case !(try (localise (map fst sig) i)) of
    Right ok =>
      case ok of
        (n, 0) => return (annotate SignatureVar (pretty n))
        (n, k) => return (annotate SignatureVar (pretty n <+> "{" <+> pretty k <+> "}"))
    Left _ =>
      return (annotate Elim (pretty $ "χ" ++ natToSuperscript i ++ " <broken index #\{show (length sig)}>"))

public export
prettyContextVar : SnocList VarName -> Nat -> M (Doc Ann)
prettyContextVar ctx i = M.do
  case !(try (localise ctx i)) of
    Right ok =>
      case ok of
        (n, 0) => return (annotate SignatureVar (pretty n))
        (n, k) => return (annotate SignatureVar (pretty n <+> "{" <+> pretty k <+> "}"))
    Left _ =>
      return (annotate Elim (pretty $ "x" ++ natToSuperscript i ++ " <broken index #\{show (length ctx)}>"))

mutual
  public export
  prettySubstContextNu' : Signature -> Omega -> SnocList VarName -> SubstContextNF -> M (Doc Ann)
  prettySubstContextNu' sig omega ctx (WkN k) = return (pretty "↑\{natToSuperscript k}")
  prettySubstContextNu' sig omega ctx (Ext sigma t) = return $ parens' $
    !(prettySubstContext' sig omega ctx sigma)
     <+>
    annotate Keyword ","
     <++>
    !(prettyElem sig omega ctx t 0)
  prettySubstContextNu' sig omega ctx Terminal = return "·"

  public export
  prettySubstContext' : Signature -> Omega -> SnocList VarName -> SubstContext -> M (Doc Ann)
  prettySubstContext' sig omega ctx sigma = prettySubstContextNu' sig omega ctx (eval sigma)

  public export
  prettySubstContext : Signature -> Omega -> SnocList VarName -> SubstContext -> M (Doc Ann)
  prettySubstContext sig omega ctx sigma = prettySubstContext' sig omega ctx sigma

  public export
  prettyTyp' : Signature
            -> Omega
            -> SnocList VarName
            -> Typ
            -> M (Doc Ann)
  prettyTyp' sig omega ctx (El a) =
    return $
      annotate Elim "El"
       <++>
      !(prettyElem sig omega ctx a 4)
  prettyTyp' sig omega ctx (PiTy x dom cod) = M.do
    case !(shrink cod 1 0) of
      Nothing => M.do
        return $
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
      Just cod => M.do
        return $
          !(prettyTyp sig omega ctx dom 3)
           <++>
          annotate Keyword "→"
           <++>
          !(prettyTyp sig omega ctx cod 2)
  prettyTyp' sig omega ctx (ImplicitPiTy x dom cod) = M.do
    return $
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
  prettyTyp' sig omega ctx (SigmaTy x dom cod) = M.do
    case !(shrink cod 1 0) of
      Nothing => M.do
        return $
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
      Just cod => M.do
        return $
          !(prettyTyp sig omega ctx dom 4)
           <++>
          annotate Keyword "⨯"
           <++>
          !(prettyTyp sig omega ctx cod 4)
  prettyTyp' sig omega ctx NatTy =
    return $ annotate Form "ℕ"
  prettyTyp' sig omega ctx ZeroTy =
    return $ annotate Form "𝟘"
  prettyTyp' sig omega ctx OneTy =
    return $ annotate Form "𝟙"
  prettyTyp' sig omega ctx UniverseTy =
    return $ annotate Form "𝕌"
  prettyTyp' sig omega ctx tm@(ContextSubstElim {}) = assert_total $ idris_crash "prettyTyp'(ContextSubstElim)"
  prettyTyp' sig omega ctx tm@(SignatureSubstElim {}) = assert_total $ idris_crash "prettyTyp'(SignatureSubstElim)"
  prettyTyp' sig omega ctx (OmegaVarElim k sigma) = M.do
    let x = annotate Elim (pretty k)
    return $
      x
       <+>
      parens' !(prettySubstContext sig omega ctx sigma)
  prettyTyp' sig omega ctx (TyEqTy l r) = return $
    !(prettyTyp sig omega ctx l 3)
     <++>
    annotate Form "≡"
     <++>
    !(prettyTyp sig omega ctx r 3)
  prettyTyp' sig omega ctx (ElEqTy l r ty) = return $
    !(prettyElem sig omega ctx l 3)
     <++>
    annotate Form "≡"
     <++>
    !(prettyElem sig omega ctx r 3)
     <++>
    annotate Form "∈"
     <++>
    !(prettyTyp sig omega ctx ty 0)
  prettyTyp' sig omega ctx (SignatureVarElim k sigma) = M.do
    x <- prettySignatureVar sig k
    return $
      x
       <+>
      parens' !(prettySubstContext sig omega ctx sigma)

  public export
  prettyTyp : Signature
           -> Omega
           -> SnocList VarName
           -> Typ
           -> Level
           -> M (Doc Ann)
  prettyTyp sig omega ctx tm lvl = M.do
    tm <- openEval sig omega tm
    wrapTyp tm lvl !(prettyTyp' sig omega ctx tm)

  public export
  prettyElem' : Signature
             -> Omega
             -> SnocList VarName
             -> Elem
             -> M (Doc Ann)
  prettyElem' sig omega ctx (PiTy x dom cod) = M.do
    case !(shrink cod 1 0) of
      Nothing => M.do
        return $
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
      Just cod => M.do
        return $
          !(prettyElem sig omega ctx dom 3)
           <++>
          annotate Keyword "→"
           <++>
          !(prettyElem sig omega ctx cod 2)
  prettyElem' sig omega ctx (ImplicitPiTy x dom cod) = M.do
    return $
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
  prettyElem' sig omega ctx (SigmaTy x dom cod) = M.do
    case !(shrink cod 1 0) of
      Nothing => M.do
        return $
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
      Just cod => M.do
        return $
          !(prettyElem sig omega ctx dom 4)
           <++>
          annotate Keyword "⨯"
           <++>
          !(prettyElem sig omega ctx cod 4)
  prettyElem' sig omega ctx (PiVal x _ _ f) =
    return $
      annotate ContextVar (pretty x)
       <++>
      annotate Intro "↦"
       <++>
      !(prettyElem sig omega (ctx :< x) f 0)
  prettyElem' sig omega ctx (ImplicitPiVal x _ _ f) =
    return $
      introBraces' (annotate ContextVar (pretty x))
       <++>
      annotate Intro "↦"
       <++>
      !(prettyElem sig omega (ctx :< x) f 0)
  prettyElem' sig omega ctx (SigmaVal _ _ _ a b) =
    return $ introParens' $
      !(prettyElem sig omega ctx a 0)
       <+>
      annotate Intro ","
       <++>
      !(prettyElem sig omega ctx b 0)
  prettyElem' sig omega ctx (PiElim f x a b e) =
    return $
      !(prettyElem sig omega ctx f 3)
       <++>
      !(prettyElem sig omega ctx e 4)
  prettyElem' sig omega ctx (ImplicitPiElim f x a b e) =
    return $
      !(prettyElem sig omega ctx f 3)
       <++>
      elimBraces' !(prettyElem sig omega ctx e 0)
  prettyElem' sig omega ctx (SigmaElim1 f x a b) =
    return $
      !(prettyElem sig omega ctx f 3)
       <++>
      annotate Elim ".π₁"
  prettyElem' sig omega ctx (SigmaElim2 f x a b) =
    return $
      !(prettyElem sig omega ctx f 3)
       <++>
      annotate Elim ".π₂"
  prettyElem' sig omega ctx NatVal0 =
    return $ annotate Intro "Z"
  prettyElem' sig omega ctx (NatVal1 e) = return $
    annotate Intro "S"
      <++>
    !(prettyElem sig omega ctx e 4)
  prettyElem' sig omega ctx NatTy =
    return $ annotate Form "ℕ"
  prettyElem' sig omega ctx ZeroTy =
    return $ annotate Form "𝟘"
  prettyElem' sig omega ctx OneTy =
    return $ annotate Form "𝟙"
  prettyElem' sig omega ctx OneVal =
    return $ annotate Intro "()"
  prettyElem' sig omega ctx (ZeroElim _ t) = M.do
    return $
      annotate Elim "𝟘-elim"
       <++>
      !(prettyElem sig omega ctx t 4)
  prettyElem' sig omega ctx (NatElim x schema z y h s t) = M.do
    return $
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
  prettyElem' sig omega ctx (SignatureVarElim k sigma) = M.do
    x <- prettySignatureVar sig k
    return $
      x
       <+>
      parens' !(prettySubstContext sig omega ctx sigma)
  prettyElem' sig omega ctx (OmegaVarElim k sigma) = M.do
    let x = annotate Elim (pretty k)
    return $
      x
       <+>
      parens' !(prettySubstContext sig omega ctx sigma)
  prettyElem' sig omega ctx (TyEqTy l r) = return $
    !(prettyElem sig omega ctx l 3)
     <++>
    annotate Form "≡"
     <++>
    !(prettyElem sig omega ctx r 3)
  prettyElem' sig omega ctx (ElEqTy l r ty) = return $
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
    return $ annotate Intro "Refl"
  prettyElem' sig omega ctx (ElEqVal _ _) =
    return $ annotate Intro "Refl"

  public export
  prettyElem : Signature
            -> Omega
            -> SnocList VarName
            -> Elem
            -> Level
            -> M (Doc Ann)
  prettyElem sig omega ctx tm lvl = M.do
    tm <- openEval sig omega tm
    wrapElem tm lvl !(prettyElem' sig omega ctx tm)

  public export
  prettyTelescope : Signature
                 -> Omega
                 -> SnocList VarName
                 -> List (VarName, Typ)
                 -> M (Doc Ann)
  prettyTelescope sig omega ctx [] = return ""
  prettyTelescope sig omega ctx ((x, ty) :: tyes) = return $
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
               -> M (Doc Ann)
  prettyContext sig omega ctx = prettyTelescope sig omega [<] (cast ctx)

  public export
  prettySignatureEntry : Signature -> Omega -> VarName -> SignatureEntry -> M (Doc Ann)
   -- Γ ⊦ χ : A
   -- Γ ⊦ χ ≔ e : A
   -- Γ ⊦ χ type
   -- Γ ⊦ χ ≔ A type
  prettySignatureEntry sig omega x (ElemEntry ctx ty) = return $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    annotate ContextVar (pretty x)
     <++>
    annotate Keyword ":"
     <++>
    !(prettyTyp sig omega (map fst ctx) ty 0)
  prettySignatureEntry sig omega x (LetElemEntry ctx e ty) = return $
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
  prettySignatureEntry sig omega x (TypeEntry ctx) = return $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    annotate ContextVar (pretty x)
     <++>
    annotate Keyword "type"
  prettySignatureEntry sig omega x (LetTypeEntry ctx e) = return $
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
  prettyConstraintEntry : Signature -> Omega -> ConstraintEntry -> M (Doc Ann)
  prettyConstraintEntry sig omega (TypeConstraint ctx a b) = M.do
   return $
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
  prettyConstraintEntry sig omega (ElemConstraint ctx a b ty) = M.do
   return $
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
  prettyConstraintEntry sig omega (SubstContextConstraint sigma tau source target) = M.do
   return $
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
  prettyConstraints : Signature -> Omega -> Constraints -> M (Doc Ann)
  prettyConstraints sig omega cs =
    return $ vsep !(forList (cast cs) (prettyConstraintEntry sig omega))

  public export
  prettySignature' : Signature -> Omega -> List (VarName, SignatureEntry) -> M (Doc Ann)
  prettySignature' sig omega [] = return ""
  prettySignature' sig omega ((x, e) :: es) = return $
    parens' !(prettySignatureEntry sig omega x e)
     <+>
    hardline
     <+>
    !(prettySignature' (sig :< (x, e)) omega es)

  public export
  prettySignature : Signature -> Omega -> Signature -> M (Doc Ann)
  prettySignature sig omega sig' = prettySignature' sig omega (toList sig')

  public export
  prettyMetaKind : MetaKind -> Doc Ann
  prettyMetaKind NoSolve = "NoSolve"
  prettyMetaKind SolveByUnification = "SolveByUnification"
  prettyMetaKind SolveByElaboration = "SolveByElaboration"

  public export
  prettyOmegaEntry : Signature -> Omega -> OmegaName -> OmegaEntry -> M (Doc Ann)
  prettyOmegaEntry sig omega n (MetaType ctx k) = M.do
   return $
    !(prettyContext sig omega ctx)
     <++>
    annotate Keyword "⊦"
     <++>
    pretty n
     <++>
    annotate Keyword "type"
     <++>
    parens' (prettyMetaKind k)
  prettyOmegaEntry sig omega n (LetType ctx rhs) = M.do
   return $
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
  prettyOmegaEntry sig omega n (MetaElem ctx ty k) = M.do
   return $
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
  prettyOmegaEntry sig omega n (LetElem ctx rhs ty) = M.do
   return $
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
  prettyOmegaEntry sig omega n (TypeConstraint ctx a b) = M.do
   return $
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
  prettyOmegaEntry sig omega n (ElemConstraint ctx a b ty) = M.do
   return $
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
  prettyOmegaEntry sig omega n (SubstContextConstraint sigma tau source target) = M.do
   return $
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
prettyOmega' : Signature -> Omega -> List (VarName, OmegaEntry) -> M (Doc Ann)
prettyOmega' sig omega [] = return ""
prettyOmega' sig omega ((x, e) :: es) = return $
  parens' !(prettyOmegaEntry sig omega x e)
   <+>
  hardline
   <+>
  !(prettyOmega' sig omega es)

public export
prettyOmega : Signature -> Omega -> M (Doc Ann)
prettyOmega sig omega = prettyOmega' sig omega (List.inorder omega)
