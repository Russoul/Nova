module ETT.Core.Assistant

-- Assistant given a (typed) signature Σ
-- Provides a set of transformations over Σ which result in a new (typed) signature Σ'

import Control.Monad.FailSt

import public Text.Parser.Fork
import Text.Lexer
import Text.Parser.CharUtil

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import ETT.Core.Language
import ETT.Core.Substitution
import ETT.Core.Conversion
import ETT.Core.Pretty
import ETT.Core.VarName

import ETT.Surface.ParserUtil

||| Signature transformation
public export
data Transformation : Type where
  ||| Σ ⇛ Σ
  Id : Transformation
  ||| Σ (?Γ ctx) ⇛ Σ
  WkCtx : VarName -> Transformation
  ||| Σ (?Γ ctx) (?Γ ⊦ ?A type) ⇛ Σ
  WkTypE : VarName -> VarName -> Transformation
  ||| Σ (?Γ ctx) (?Γ ⊦ ?A type) (?Γ ⊦ ?x : ?A) ⇛ Σ
  WkElem : VarName -> VarName -> VarName -> Transformation
  ||| Σ (?Γ ctx) (?Γ ⊦ ?A type) (?Γ ⊦ ?e : ?A) (?Γ ⊦ ?x ≔ ?e : ?A) ⇛ Σ
  WkLetElem : VarName -> VarName -> VarName -> VarName -> Transformation
  ||| Σ₀ Σ₁(ε/?Γ) ⇒ Σ₀ (?Γ ctx) Σ₁
  InstCtxEmpty : VarName -> Transformation
  ||| Σ₀ (?Γ ctx) (?Γ ⊦ ?A type) Σ₁(?Γ (x : ?A) / ?Γ) ⇒ Σ₀ (?Γ ctx) Σ₁
  InstCtxCons : (contextName : VarName) -> (newContextName : VarName) -> (typeName : VarName) -> (binderName : VarName) -> Transformation
  ||| Σ₀ (Γ ⊦ ?X type) (Γ ⊦ ?Y type) Σ₁(?X → ?Y / ?A) ⇒ Σ₀ (Γ ⊦ ?A type) Σ₁
  InstTypEExp : (solveMe : VarName) -> (dom : VarName) -> (cod : VarName) -> Transformation
  ||| Σ₀ (Γ ⊦ ?X type) (Γ (x : ?X) ⊦ ?Y type) Σ₁((x : ?X) → ?Y / ?A) ⇒ Σ₀ (Γ ⊦ ?A type) Σ₁
  InstTypEPi : (solveMe : VarName) -> (dom : VarName) -> (x : VarName) -> (cod : VarName) -> Transformation
  ||| Σ₀ (Γ (x : A) ⊦ f : B) Σ₁((x ↦ f) / f) ⇒ Σ₀ (Γ ⊦ f : (x : A) → B) Σ₁
  InstElemLam : (solveMe : VarName) -> (newName : VarName) -> Transformation
  ||| Σ₀ Σ₁(ℕ/?A) ⇒ Σ₀ (Γ ⊦ ?A type) Σ₁
  InstTypENat : (solveMe : VarName) -> Transformation
  ||| Σ₀ Σ₁(𝕌/?A) ⇒ Σ₀ (Γ ⊦ ?A type) Σ₁
  InstTypEUniverse : (solveMe : VarName) -> Transformation
  ||| Σ₀ (x : 𝕌) Σ₁(El x/?A) ⇒ Σ₀ (Γ ⊦ ?A type) Σ₁
  InstTypEEl : (solveMe : VarName) -> (x : VarName) -> Transformation
  ||| Σ₀ (Γ ⊦ ?A type) (Γ ⊦ ?a₀ : ?A) (Γ ⊦ ?a₁ : ?A) Σ₁(?a₀ ≡ ?a₁ ∈ ?A / ?A) ⇒ Σ₀ (Γ ⊦ ?A type) Σ₁
  InstTypEEq : (solveMe : VarName) -> (typeName : VarName) -> (leftName : VarName) -> (rightName : VarName) -> Transformation
  ||| Σ₀ Σ₁(γ₀.x.γ₁.x / χ) ⇛ Σ₀ (Γ₀ (x : A) Γ₁ ⊦ χ : A) Σ₁
  InstContextVar : (solveMe : VarName) -> (contextVar : VarName) -> Transformation
  RenameSigVar : Nat -> VarName -> Transformation
  RenameCtxVar : Nat -> Nat -> VarName -> Transformation
  ||| Σ₀ (Γ ⊦ X type) (Γ (x : X) ⊦ Y type) (Γ ⊦ f : (x : X) → Y) (Γ ⊦ e : X) (Γ ⊦ Y(e/x) = A type) ⇒ Σ₀ (Γ ⊦ x : A) Σ₁
  InstPiElim : (solveMe, dom, x, cod, f, e, eq : VarName) -> Transformation
  ||| Σ₀ Σ₁(*/α) ⇒ Σ₀ (Γ ⊦ [α] A = A type) Σ₁
  InstTyRefl : VarName -> Transformation
  ||| Σ₀ (Γ (x : A) ⊦ β : f x ≡ g x ∈ B) Σ₁ ⇒ Σ₀ (Γ ⊦ α : f ≡ g ∈ (x : A) → B) Σ₁
  FunExt : (alpha, x, beta : VarName) -> Transformation
  ||| Σ ⇒ Σ E
  DebugDropLast : Transformation


funTy : TypE -> TypE -> TypE
funTy a b = PiTy "_" a (ContextSubstElim b Wk)

||| Γ₀ (xᵢ : A) Γ₁ ⊦ xᵢ : A
lookupContext : Context -> VarName -> Maybe (Elem, TypE)
lookupContext Empty x = Nothing
lookupContext (SignatureVarElim i) x = Nothing
lookupContext (Ext ctx x ty) y = FailSt.do
  case x == y of
    True => Just (ContextVarElim 0, ContextSubstElim ty Wk)
    False => do
      (t, ty) <- lookupContext ctx y
      Just (ContextSubstElim t Wk, ContextSubstElim ty Wk)

splitByVarName : Signature -> VarName -> M (Signature, SignatureEntry, Signature)
splitByVarName [<] x = throw "Can't find \{x} in the signature"
splitByVarName (sig :< (v, e)) x = FailSt.do
  case v == x of
    True => return (sig, e, [<])
    False => FailSt.do
      (sig0, entry, sig1) <- splitByVarName sig x
      return (sig0, entry, sig1 :< (v, e))

splitByIndex : Signature -> Nat -> M (Signature, VarName, SignatureEntry, Signature)
splitByIndex [<] x = throw "index out of bounds"
splitByIndex (sig :< (v, e)) 0 = FailSt.do
  return (sig, v, e, [<])
splitByIndex (sig :< (v, e)) (S k) = FailSt.do
  (sig0, x, entry, sig1) <- splitByIndex sig k
  return (sig0, x, entry, sig1 :< (v, e))

public export
compute : (target : Signature) -> Transformation -> M Signature
compute target Id = FailSt.do
  io $ putStrLn "Signature length: \{show $ length $ target}"
  io $ putStrLn (renderDocTerm !(prettySignature [<] target))
  return target
compute target (WkCtx ctxN) = return (target :< (ctxN, CtxEntry))
compute target (WkTypE ctxN typeN) = return (target :< (ctxN, CtxEntry) :< (typeN, TypEEntry Var))
compute target (WkElem ctxN typeN elemN) =
  -- Σ (Γ ctx) (Γ ⊦ A type) Γ ⊦ A type
  -- Σ (Γ ctx) (Γ ⊦ A type) (Γ ⊦ a : A)
  return $
    target :< (ctxN, CtxEntry) :< (typeN, TypEEntry Var) :< (elemN, ElemEntry (VarN 1) (SignatureVarElim 0 Id))
compute target (WkLetElem ctxN typeN elemN letN) =
  -- Σ (Γ ctx) (Γ ⊦ A type) Γ ⊦ A type
  -- Σ (Γ ctx) (Γ ⊦ A type) (Γ ⊦ a : A)
  return $
    target
      :<
    (ctxN, CtxEntry)
      :<
    (typeN, TypEEntry Var)
      :<
    (elemN, ElemEntry (VarN 1) (SignatureVarElim 0 Id))
      :<
    (letN, LetElemEntry (VarN 2) (SignatureVarElim 0 Id) (SignatureVarElim 1 Id))
compute target (InstCtxEmpty x) = FailSt.do
  -- Σ₀ (A ctx) ⊦ Σ₁
  -- Σ₀ ⊦ Σ₁(id, ε)
  (sig0, CtxEntry, sig1) <- splitByVarName target x
    | _ => throw "\{x} is not a 'ctx' entry"
  return (sig0 ++ subst sig1 (Ext Id (CtxEntryInstance Empty)))
compute target (InstCtxCons ctxN newCtxN typeN binderN) = FailSt.do
  -- Σ₀ (Γ ctx) ⊦ Σ₁
  -- Σ₀ (Γ ctx) (Γ ⊦ A type) ⊦ Σ₁(↑², Γ (x : A))
  (sig0, CtxEntry, sig1) <- splitByVarName target ctxN
    | _ => throw "\{ctxN} is not a 'ctx' entry"
  return ((sig0 :< (newCtxN, CtxEntry) :< (typeN, TypEEntry Var))
            ++
          Signature.subst sig1 (Ext (WkN 2) (CtxEntryInstance $ Ext (VarN 1) binderN Var))
         )
compute target (InstTypEExp solveMe dom cod) = FailSt.do
  -- Σ₀ (Γ ⊦ A type) ⊦ Σ₁
  -- Σ₀ (Γ ⊦ A type) (Γ(↑) ⊦ B type) ⊦ Σ₁(↑², A₁ → B₀)
  (sig0, TypEEntry ctx, sig1) <- splitByVarName target solveMe
    | _ => throw "\{solveMe} is not a 'type' entry"
  return $ (sig0 :< (dom, TypEEntry ctx)) :< (cod, TypEEntry (subst ctx (the SubstSignature Wk)))
             ++
           Signature.subst sig1 (Ext (WkN 2)
             (TypEEntryInstance $ funTy (SignatureVarElim 1 Id) (SignatureVarElim 0 Id)))
compute target (InstTypEPi solveMe dom x cod) = FailSt.do
  -- Σ₀ (Γ ⊦ A type) ⊦ Σ₁
  -- Σ₀ (Γ ⊦ A type) (Γ(↑) (x : A) ⊦ B type) ⊦ Σ₁(↑², (x : A₁) → B₀)
  (sig0, TypEEntry ctx, sig1) <- splitByVarName target solveMe
    | _ => throw "\{solveMe} is not a 'type' entry"
  return $ (sig0 :< (dom, TypEEntry ctx)) :< (cod, TypEEntry $ Ext (subst ctx (the SubstSignature Wk)) x (SignatureVarElim 0 Id))
             ++
           Signature.subst sig1
             (Ext (WkN 2)
                  (TypEEntryInstance $ PiTy x
                                        (SignatureVarElim 1 Id)
                                        (SignatureVarElim 0 Id)
                  )
             )
compute target (InstTypENat x) = FailSt.do
  -- Σ₀ (Γ ⊦ χ type) ⊦ Σ₁
  -- Σ₀ ⊦ Σ₁(id, ℕ)
  (sig0, TypEEntry ctx, sig1) <- splitByVarName target x
    | _ => throw "\{x} is not a 'type' entry"
  return (sig0 ++ subst sig1 (Ext Id (TypEEntryInstance NatTy)))
compute target (InstTypEUniverse x) = FailSt.do
  -- Σ₀ (Γ ⊦ χ type) ⊦ Σ₁
  -- Σ₀ ⊦ Σ₁(id, 𝕌)
  (sig0, TypEEntry ctx, sig1) <- splitByVarName target x
    | _ => throw "\{x} is not a 'type' entry"
  return (sig0 ++ subst sig1 (Ext Id (TypEEntryInstance UniverseTy)))
compute target (InstTypEEl solveN typeN) = FailSt.do
  -- Σ₀ (Γ ⊦ χ type) ⊦ Σ₁
  -- Σ₀ (Γ ⊦ A : 𝕌) ⊦ Σ₁(↑, El A₀)
  (sig0, TypEEntry ctx, sig1) <- splitByVarName target solveN
    | _ => throw "\{solveN} is not a 'type' entry"
  return (sig0 :< (typeN, ElemEntry ctx UniverseTy) ++ subst sig1 (Ext Wk (TypEEntryInstance $ El (SignatureVarElim 0 Id))))
compute target (InstTypEEq solveN typeN leftN rightN) = FailSt.do
  -- Σ₀ (Γ ⊦ A type) ⊦ Σ₁
  -- Σ₀ (Γ ⊦ A type) (Γ(↑) ⊦ a₀ : A) (Γ(↑²) ⊦ a₁ : A) ⊦ Σ₁(↑³, a₀ ≡ a₁ ∈ A)
  (sig0, TypEEntry ctx, sig1) <- splitByVarName target solveN
    | _ => throw "\{solveN} is not a 'type' entry"
  let ctx' = subst ctx (the SubstSignature Wk)
  let ctx'' = subst ctx (the SubstSignature (Chain Wk Wk))
  let ctx''' = subst ctx (the SubstSignature (Chain (Chain Wk Wk) Wk))
  return $ (sig0 :< (typeN, TypEEntry ctx) :< (leftN, ElemEntry ctx' Var) :< (rightN, ElemEntry ctx'' (SignatureVarElim 1 Id)))
             ++
           Signature.subst sig1 (Ext (WkN 3) (TypEEntryInstance $ EqTy (SignatureVarElim 1 Id) (SignatureVarElim 0 Id) (SignatureVarElim 2 Id)))
compute target (InstElemLam solveN newN) = FailSt.do
  -- Σ₀ (Γ ⊦ f : (x : A) → B) ⊦ Σ₁
  -- Σ₀ (Γ (x : A) ⊦ f : B) ⊦ Σ₁(↑, λ x A(↑) B(↑) f)
  (sig0, ElemEntry ctx ty, sig1) <- splitByVarName target solveN
    | _ => throw "\{solveN} is not an 'elem' entry"
  let PiTy x a b = runSubst ty
    | _ => throw "\{solveN} is not a Π-type"
  let ctx' = subst (Ext ctx x a) Wk
  return $
    sig0 :< (newN, ElemEntry ctx' b)
      ++
    subst sig1 (Ext Wk (ElemEntryInstance $ PiVal x (SignatureSubstElim a Wk) (SignatureSubstElim b Wk) (SignatureVarElim 0 Id)))
compute target (InstContextVar solveN varN) = FailSt.do
  --  Σ₀ (Γ₀ (x : A) Γ₁ ⊦ χ : A) ⊦ Σ₁
  (sig0, ElemEntry ctx ty, sig1) <- splitByVarName target solveN
    | _ => throw "\{solveN} is not a 'elem' entry"
  let Just (sol, gotTy) = lookupContext ctx varN
    | Nothing => throw "Undefined context name: \{varN}"
  True <- conv ty gotTy
    | False => throw "Context variable's type doesn't match the expected type"
  return $
    sig0 ++ subst sig1 (Ext Id (ElemEntryInstance sol))
compute target (RenameSigVar i x) = FailSt.do
  (sig0, _, e, sig1) <- splitByIndex target i
  return (extend sig0 x e ++ sig1)
compute target (RenameCtxVar i j x) = FailSt.do
  (sig0, n, e, sig1) <- splitByIndex target i
  return (extend sig0 n !(renameEntry e j x) ++ sig1)
 where
  renameCtx : Context -> Nat -> VarName -> M Context
  renameCtx Empty i x = throw "index out of bounds"
  renameCtx (Ext ctx _ ty) 0 x = return $ Ext ctx x ty
  renameCtx (Ext ctx x' ty) (S i) x = return $ Ext !(renameCtx ctx i x) x' ty
  renameCtx (SignatureVarElim k) i x = throw "index out of bounds"

  renameEntry : SignatureEntry -> Nat -> VarName -> M SignatureEntry
  renameEntry CtxEntry j x = throw "Can't rename here"
  renameEntry (TypEEntry ctx) j x = return $ TypEEntry !(renameCtx ctx j x)
  renameEntry (ElemEntry ctx ty) j x = return $ ElemEntry !(renameCtx ctx j x) ty
  renameEntry (LetElemEntry ctx e ty) j x = return $ LetElemEntry !(renameCtx ctx j x) e ty
  renameEntry (EqTyEntry ctx a b) j x = return $ EqTyEntry !(renameCtx ctx j x) a b
compute target (InstPiElim n dom x cod f e eq) = FailSt.do
   -- Σ₀ ⊦ Γ ctx
   -- Σ₀ Γ ⊦ A type
   -- Σ₀ Γ ⊦ t : A
   -- Σ₀ (Γ ⊦ X type) (Γ (x : X) ⊦ Y type) (Γ ⊦ f : (x : X) → Y) (Γ ⊦ e : X) (Γ ⊦ Y(e/x) = A type) Σ₁(ap f x X Y e / t) ⇒ Σ₀ (Γ ⊦ t : A) Σ₁
   -- Σ₀ (Γ ⊦ X type) (Γ(↑) (x : χ₀) ⊦ Y type) (Γ(↑²) ⊦ f : (x : X₁) → Y₀) (Γ(↑³) ⊦ e : X₂) (Γ(↑⁴) ⊦ Y₂(id, e₀) = A(↑⁴) type)
   --     Σ₁(↑⁵, ap f₂ x X₄ Y₃ e₁)
  (sig0, ElemEntry ctx ty, sig1) <- splitByVarName target n
    | _ => throw "\{n} is not a 'elem' entry"
  let sig = extend (extend sig0 dom (TypEEntry ctx)) cod (TypEEntry (Ext (subst ctx Wk) x Var))
  let sig = extend sig f (ElemEntry (subst ctx (WkN 2)) (PiTy x (VarN 1) Var))
  let sig = extend sig e (ElemEntry (subst ctx (WkN 3)) (VarN 2))
  let sig = extend sig eq (EqTyEntry (subst ctx (WkN 4)) (SignatureVarElim 2 (Ext Id SigVar)) (SignatureSubstElim ty (WkN 4)))
  let sig = sig ++ subst sig1 (Ext (WkN 5) (ElemEntryInstance $ PiElim (SigVarN 2) x (VarN 4) (VarN 3) (SigVarN 1)))
  return sig
compute target (InstTyRefl n) = FailSt.do
  (sig0, EqTyEntry ctx a b, sig1) <- splitByVarName target n
    | _ => throw "\{n} is not a '_ = _ type' entry"
  True <- conv a b
    | _ => throw "\{n} is not a reflexive equality"
  return (sig0 ++ subst sig1 (Ext Id EqTyEntryInstance))
compute target (FunExt alpha x beta) = FailSt.do
  -- Σ₀ (Γ (x : A) ⊦ β : f x ≡ g x ∈ B) Σ₁ ⇒ Σ₀ (Γ ⊦ α : f ≡ g ∈ (x : A) → B) Σ₁
  -- Σ₀ (Γ (x : A) ⊦ β : ap f(↑) A(↑) B(↑⁺) x₀ ≡ g(↑) x₀ ∈ B) Σ₁(↑, *)
  (sig0, ElemEntry ctx ty, sig1) <- splitByVarName target alpha
    | _ => throw "\{alpha} is not an 'elem' entry"
  let EqTy lhs rhs ty = runSubst ty
    | _ => throw "Not an equality type"
  let PiTy v a b = runSubst ty
    | _ => throw "Not a function type"
  let ctx' = Ext ctx x a
  let sig = extend sig0 beta
             (ElemEntry ctx'
               (EqTy (PiElim (ContextSubstElim lhs Wk) v (ContextSubstElim a Wk) (ContextSubstElim b (Under Wk)) CtxVar)
                     (PiElim (ContextSubstElim rhs Wk) v (ContextSubstElim a Wk) (ContextSubstElim b (Under Wk)) CtxVar)
                     b
               )
             )
  return (sig ++ subst sig1 (Ext Wk (ElemEntryInstance EqVal)))
compute (xs :< _) DebugDropLast = FailSt.do
  return xs
compute [<] DebugDropLast = FailSt.do
  throw "debug-drop-last: Signature is empty"


public export
computeN : Signature -> List Transformation -> M Signature
computeN sig [] = return sig
computeN sig (x :: xs) = computeN !(compute sig x) xs

public export
id : Rule Transformation
id = delim_ "id" $> Id

public export
wkCtx : Rule Transformation
wkCtx = do
  delim_ "wk-ctx"
  spaceDelim
  v <- varName
  pure (WkCtx v)

public export
wkTypE : Rule Transformation
wkTypE = do
  delim_ "wk-type"
  spaceDelim
  v0 <- varName
  spaceDelim
  v1 <- varName
  pure (WkTypE v0 v1)

public export
wkElem : Rule Transformation
wkElem = do
  delim_ "wk-elem"
  spaceDelim
  v0 <- varName
  spaceDelim
  v1 <- varName
  spaceDelim
  v2 <- varName
  pure (WkElem v0 v1 v2)

public export
wkLetElem : Rule Transformation
wkLetElem = do
  delim_ "wk-let-elem"
  spaceDelim
  v0 <- varName
  spaceDelim
  v1 <- varName
  spaceDelim
  v2 <- varName
  spaceDelim
  v3 <- varName
  pure (WkLetElem v0 v1 v2 v3)

public export
instCtxEmpty : Rule Transformation
instCtxEmpty = do
  delim_ "inst-ctx-empty"
  spaceDelim
  x <- varName
  pure (InstCtxEmpty x)

public export
instCtxCons : Rule Transformation
instCtxCons = do
  delim_ "inst-ctx-cons"
  spaceDelim
  x <- varName
  spaceDelim
  y <- varName
  spaceDelim
  z <- varName
  spaceDelim
  w <- varName
  pure (InstCtxCons x y z w)

public export
instTypEExp : Rule Transformation
instTypEExp = do
  delim_ "inst-exp"
  spaceDelim
  x <- varName
  spaceDelim
  y <- varName
  spaceDelim
  z <- varName
  pure (InstTypEExp x y z)

public export
instTypEPi : Rule Transformation
instTypEPi = do
  delim_ "inst-pi"
  spaceDelim
  x <- varName
  spaceDelim
  y <- varName
  spaceDelim
  z <- varName
  spaceDelim
  w <- varName
  pure (InstTypEPi x y z w)

public export
instTypENat : Rule Transformation
instTypENat = do
  delim_ "inst-nat"
  spaceDelim
  x <- varName
  pure (InstTypENat x)

public export
instTypEUniverse : Rule Transformation
instTypEUniverse = do
  delim_ "inst-universe"
  spaceDelim
  x <- varName
  pure (InstTypEUniverse x)

public export
instTypEEl : Rule Transformation
instTypEEl = do
  delim_ "inst-el"
  spaceDelim
  x <- varName
  spaceDelim
  y <- varName
  pure (InstTypEEl x y)

public export
instElemLam : Rule Transformation
instElemLam = do
  delim_ "inst-lam"
  spaceDelim
  x <- varName
  spaceDelim
  y <- varName
  pure (InstElemLam x y)

public export
instTypEEq : Rule Transformation
instTypEEq = do
  delim_ "inst-eq"
  spaceDelim
  x <- varName
  spaceDelim
  y <- varName
  spaceDelim
  z <- varName
  spaceDelim
  w <- varName
  pure (InstTypEEq x y z w)

public export
instContextVar : Rule Transformation
instContextVar = do
  delim_ "inst-ctx-var"
  spaceDelim
  x <- varName
  spaceDelim
  y <- varName
  pure (InstContextVar x y)

public export
renameSignatureVar : Rule Transformation
renameSignatureVar = do
  delim_ "rename-sig-var"
  spaceDelim
  x <- nat
  spaceDelim
  y <- varName
  pure (RenameSigVar x y)

public export
renameContextVar : Rule Transformation
renameContextVar = do
  delim_ "rename-ctx-var"
  spaceDelim
  x <- nat
  spaceDelim
  y <- nat
  spaceDelim
  z <- varName
  pure (RenameCtxVar x y z)

public export
instPiElim : Rule Transformation
instPiElim = do
  delim_ "inst-pi-elim"
  spaceDelim
  n <- varName
  spaceDelim
  dom <- varName
  spaceDelim
  x <- varName
  spaceDelim
  cod <- varName
  spaceDelim
  f <- varName
  spaceDelim
  e <- varName
  spaceDelim
  eq <- varName
  pure (InstPiElim n dom x cod f e eq)

public export
instTyRefl : Rule Transformation
instTyRefl = do
  delim_ "inst-ty-refl"
  spaceDelim
  n <- varName
  pure (InstTyRefl n)

public export
funExt : Rule Transformation
funExt = do
  delim_ "fun-ext"
  spaceDelim
  x <- varName
  spaceDelim
  y <- varName
  spaceDelim
  z <- varName
  pure (FunExt x y z)

public export
debugDropLast : Rule Transformation
debugDropLast = do
  delim_ "debug-drop-last"
  pure DebugDropLast

public export
transformation : Rule Transformation
transformation = id
             <|> wkCtx
             <|> wkTypE
             <|> wkElem
             <|> wkLetElem
             <|> instCtxEmpty
             <|> instCtxCons
             <|> instTypEExp
             <|> instTypEPi
             <|> instTypENat
             <|> instTypEUniverse
             <|> instTypEEl
             <|> instElemLam
             <|> instTypEEq
             <|> instContextVar
             <|> renameSignatureVar
             <|> renameContextVar
             <|> instPiElim
             <|> instTyRefl
             <|> funExt
             <|> debugDropLast
