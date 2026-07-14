module Nova.Foundation.Derivation.NamedPretty

-- Named surface syntax pretty-printer (see docs/NovaNamedSyntax.txt).
--
-- Mirrors Nova.Foundation.Pretty exactly, except every binder position
-- prints a name instead of leaving it implicit in ☐ₙ. There is no stored
-- name to recover for most of these (Ctx/Ty/Elem carry no name info at
-- all) — this printer *invents* one, deterministically, from the
-- position's type and what's already in scope (see `freshName` below).
-- Session.idr stores `ctx-ext` lines verbatim (the exact text the AI
-- wrote), so a variable's *authored* name is never lost in the session
-- file itself; this printer's invented names only ever show up in
-- terminal output (apply's echoed facts, `dump`, rejection messages) and
-- deliberately mimic the same n/m/k, A/B/C, v/w/u convention a human
-- would likely pick, so in practice they usually read close to what was
-- actually typed.

import Data.SnocList
import Data.Maybe

import Nova.Foundation.Syntax
import Nova.Foundation.Derivation
import Nova.Foundation.Derivation.NamedParser
import Nova.Foundation.Pretty

%default covering

-- ===== Name environment (reverse) lookup =====

||| The name at a given de Bruijn index, if in range. Out-of-range only
||| happens for malformed input; falls back to a visibly-synthetic marker
||| rather than crashing.
export
nameAt : NameEnv -> Nat -> String
nameAt env n = fromMaybe ("?" ++ show n) (go env n)
  where
    go : NameEnv -> Nat -> Maybe String
    go [<] _ = Nothing
    go (_ :< x) Z = Just x
    go (rest :< _) (S k) = go rest k

-- ===== Fresh name invention =====

candidatesNat : List String
candidatesNat = ["n", "m", "k", "i", "j"]

candidatesUniv : List String
candidatesUniv = ["A", "B", "C", "D"]

candidatesEl : List String
candidatesEl = ["v", "w", "u", "t"]

candidatesIH : List String
candidatesIH = ["ih", "rec", "p", "q"]

candidatesGeneric : List String
candidatesGeneric = ["x", "y", "z", "w", "v"]

used : NameEnv -> String -> Bool
used env name = isJust (resolveName env name)

freshNumbered : String -> Nat -> NameEnv -> String
freshNumbered base n env =
  let candidate = base ++ show n in
  if used env candidate then freshNumbered base (S n) env else candidate

freshFromList : List String -> NameEnv -> String
freshFromList cs env = go cs
  where
    go : List String -> String
    go [] = freshNumbered (case cs of (c :: _) => c; [] => "x") 1 env
    go (c :: rest) = if used env c then go rest else c

||| Invent a name for a fresh binder given its type, not colliding with
||| anything currently in scope. Biased by type for readability, matching
||| the convention used throughout derivations/* (n/m/k for ℕ, A/B/C for
||| 𝕌, v/w/u for El-typed slots).
export
freshForTy : Ty -> NameEnv -> String
freshForTy NatTy = freshFromList candidatesNat
freshForTy UniverseTy = freshFromList candidatesUniv
freshForTy (El _) = freshFromList candidatesEl
freshForTy _ = freshFromList candidatesGeneric

export
freshGeneric : NameEnv -> String
freshGeneric = freshFromList candidatesGeneric

export
freshIH : NameEnv -> String
freshIH = freshFromList candidatesIH

-- ===== Occurs check =====
--
-- Whether de Bruijn index `k` appears free in a Ty/Elem/SubNorm — used to
-- decide whether a Pi/Sigma binder can use the `A → B`/`A ⨯ B` sugar
-- (dropping the name entirely) instead of `(x:A) → B`/`(x:A) ⨯ B`: if the
-- codomain never references the domain's bound variable, there's nothing
-- to name. Mirrors the printer's own binder-depth bookkeeping exactly —
-- each nested binder increments `k` by however many slots it introduces.

mutual
  usesIndexTy : Nat -> Ty -> Bool
  usesIndexTy k Ty.ZeroTy = False
  usesIndexTy k Ty.OneTy = False
  usesIndexTy k Ty.NatTy = False
  usesIndexTy k Ty.UniverseTy = False
  usesIndexTy k (Ty.PiTy a b) = usesIndexTy k a || usesIndexTy (S k) b
  usesIndexTy k (Ty.SigmaTy a b) = usesIndexTy k a || usesIndexTy (S k) b
  usesIndexTy k (Ty.EqTy e0 e1 a) = usesIndexElem k e0 || usesIndexElem k e1 || usesIndexTy k a
  usesIndexTy k (El e) = usesIndexElem k e
  usesIndexTy k (Quotient a r) = usesIndexTy k a || usesIndexTy (S (S k)) r

  usesIndexElem : Nat -> Elem -> Bool
  usesIndexElem k (CtxVar n) = n == k
  usesIndexElem k (ZeroElim e) = usesIndexElem k e
  usesIndexElem k OneIntro = False
  usesIndexElem k NatIntro0 = False
  usesIndexElem k (NatIntro1 e) = usesIndexElem k e
  usesIndexElem k (NatElim z s t) = usesIndexElem k z || usesIndexElem (S (S k)) s || usesIndexElem k t
  usesIndexElem k (PiIntro e) = usesIndexElem (S k) e
  usesIndexElem k (PiApp f e) = usesIndexElem k f || usesIndexElem k e
  usesIndexElem k (SigmaIntro e e') = usesIndexElem k e || usesIndexElem k e'
  usesIndexElem k (SigmaElim1 e) = usesIndexElem k e
  usesIndexElem k (SigmaElim2 e) = usesIndexElem k e
  usesIndexElem k Elem.ZeroTy = False
  usesIndexElem k Elem.OneTy = False
  usesIndexElem k Elem.NatTy = False
  usesIndexElem k (Elem.PiTy e e') = usesIndexElem k e || usesIndexElem (S k) e'
  usesIndexElem k (Elem.SigmaTy e e') = usesIndexElem k e || usesIndexElem (S k) e'
  usesIndexElem k (Elem.EqTy e0 e1 e2) = usesIndexElem k e0 || usesIndexElem k e1 || usesIndexElem k e2
  usesIndexElem k Refl = False
  usesIndexElem k (SigVar x es) = usesIndexSubNorm k es
  usesIndexElem k (Class a) = usesIndexElem k a
  usesIndexElem k (QuotElim f q) = usesIndexElem k f || usesIndexElem k q

  usesIndexSubNorm : Nat -> SubNorm -> Bool
  usesIndexSubNorm k [<] = False
  usesIndexSubNorm k (es :< e) = usesIndexSubNorm k es || usesIndexElem k e

-- ===== Sub and Elem (mutually recursive) =====

mutual
  export
  prettySubN : NameEnv -> Sub -> String
  prettySubN env (Ext s e) = prettySubN env s ++ ", " ++ prettyElemNoCommaN env e
  prettySubN env s = prettySubChainN env s

  prettySubChainN : NameEnv -> Sub -> String
  prettySubChainN env (Chain s t) = prettySubAtomN env s ++ " ∘ " ++ prettySubChainN env t
  prettySubChainN env s = prettySubAtomN env s

  prettySubAtomN : NameEnv -> Sub -> String
  prettySubAtomN env Terminal = "·"
  prettySubAtomN env Id = "id"
  prettySubAtomN env Wk = "↑"
  prettySubAtomN env s = "(" ++ prettySubN env s ++ ")"

  export
  prettyElemN : NameEnv -> Elem -> String
  prettyElemN env (SigmaIntro e e') = prettyElemNoCommaN env e ++ ", " ++ prettyElemN env e'
  prettyElemN env e = prettyElemNoCommaN env e

  export
  prettyElemNoCommaN : NameEnv -> Elem -> String
  prettyElemNoCommaN env (Elem.PiTy e e') =
    if usesIndexElem 0 e'
      then let x = freshGeneric env
           in "(" ++ x ++ ":" ++ prettyElemPrefixN env e ++ ") → " ++ prettyElemNoCommaN (env :< x) e'
      else prettyElemPrefixN env e ++ " → " ++ prettyElemNoCommaN (env :< wildcard) e'
  prettyElemNoCommaN env (Elem.SigmaTy e e') =
    if usesIndexElem 0 e'
      then let x = freshGeneric env
           in "(" ++ x ++ ":" ++ prettyElemPrefixN env e ++ ") ⨯ " ++ prettyElemNoCommaN (env :< x) e'
      else prettyElemPrefixN env e ++ " ⨯ " ++ prettyElemNoCommaN (env :< wildcard) e'
  prettyElemNoCommaN env (Elem.EqTy e0 e1 e2) =
    prettyElemPrefixN env e0 ++ " ≡ " ++ prettyElemPrefixN env e1 ++ " ∈ " ++ prettyElemPrefixN env e2
  prettyElemNoCommaN env e = prettyElemPrefixN env e

  prettyElemPrefixN : NameEnv -> Elem -> String
  prettyElemPrefixN env (PiIntro e) =
    let x = freshGeneric env
    in "λ" ++ x ++ ". " ++ prettyElemPostfixN (env :< x) e
  prettyElemPrefixN env (ZeroElim e) = "𝟘-elim " ++ prettyElemAtomN env e
  prettyElemPrefixN env (NatIntro1 e) = "S " ++ prettyElemAtomN env e
  prettyElemPrefixN env (NatElim z s t) =
    let n  = freshFromList candidatesNat env
        ih = freshIH (env :< n)
    in "ℕ-elim " ++ prettyElemAtomN env z ++
       " (" ++ n ++ " " ++ ih ++ ". " ++ prettyElemAtomN (env :< n :< ih) s ++ ") " ++
       prettyElemAtomN env t
  prettyElemPrefixN env (Class a) = "class " ++ prettyElemAtomN env a
  prettyElemPrefixN env (QuotElim f q) = "quot-elim " ++ prettyElemAtomN env f ++ " " ++ prettyElemAtomN env q
  prettyElemPrefixN env e = prettyElemPostfixN env e

  prettyElemPostfixN : NameEnv -> Elem -> String
  prettyElemPostfixN env (SigmaElim1 e) = prettyElemPostfixN env e ++ " .π₁"
  prettyElemPostfixN env (SigmaElim2 e) = prettyElemPostfixN env e ++ " .π₂"
  prettyElemPostfixN env (PiApp f e) = prettyElemPostfixN env f ++ " " ++ prettyElemAtomN env e
  prettyElemPostfixN env e = prettyElemAtomN env e

  export
  prettyElemAtomN : NameEnv -> Elem -> String
  prettyElemAtomN env (CtxVar n) = nameAt env n
  prettyElemAtomN env OneIntro = "()"
  prettyElemAtomN env NatIntro0 = "Z"
  prettyElemAtomN env Refl = "Refl"
  prettyElemAtomN env Elem.ZeroTy = "𝟘"
  prettyElemAtomN env Elem.OneTy = "𝟙"
  prettyElemAtomN env Elem.NatTy = "ℕ"
  prettyElemAtomN env (SigVar x es) = x ++ "[" ++ prettySubNormN env es ++ "]"
  prettyElemAtomN env e = "(" ++ prettyElemN env e ++ ")"

  ||| t˲ ::= · | t˲ , t
  export
  prettySubNormN : NameEnv -> SubNorm -> String
  prettySubNormN env [<] = "·"
  prettySubNormN env (es :< e) = prettySubNormN env es ++ ", " ++ prettyElemNoCommaN env e

-- ===== Ty =====

mutual
  export
  prettyTyN : NameEnv -> Ty -> String
  prettyTyN env (Ty.EqTy e0 e1 a) =
    prettyElemAtomN env e0 ++ " ≡ " ++ prettyElemAtomN env e1 ++ " ∈ " ++ prettyTyArrowN env a
  prettyTyN env ty = prettyTyArrowN env ty

  prettyTyArrowN : NameEnv -> Ty -> String
  prettyTyArrowN env (Ty.PiTy a b) =
    if usesIndexTy 0 b
      then let x = freshForTy a env
           in "(" ++ x ++ ":" ++ prettyTyElN env a ++ ") → " ++ prettyTyArrowN (env :< x) b
      else prettyTyElN env a ++ " → " ++ prettyTyArrowN (env :< wildcard) b
  prettyTyArrowN env (Ty.SigmaTy a b) =
    if usesIndexTy 0 b
      then let x = freshForTy a env
           in "(" ++ x ++ ":" ++ prettyTyElN env a ++ ") ⨯ " ++ prettyTyArrowN (env :< x) b
      else prettyTyElN env a ++ " ⨯ " ++ prettyTyArrowN (env :< wildcard) b
  prettyTyArrowN env (Ty.Quotient a r) =
    let x = freshForTy a env
        y = freshGeneric (env :< x)
    in prettyTyElN env a ++ " / (" ++ x ++ " " ++ y ++ ". " ++ prettyTyArrowN (env :< x :< y) r ++ ")"
  prettyTyArrowN env ty = prettyTyElN env ty

  prettyTyElN : NameEnv -> Ty -> String
  prettyTyElN env (El e) = "El " ++ prettyElemAtomN env e
  prettyTyElN env ty = prettyTyAtomN env ty

  prettyTyAtomN : NameEnv -> Ty -> String
  prettyTyAtomN env Ty.ZeroTy = "𝟘"
  prettyTyAtomN env Ty.OneTy = "𝟙"
  prettyTyAtomN env Ty.NatTy = "ℕ"
  prettyTyAtomN env Ty.UniverseTy = "𝕌"
  prettyTyAtomN env ty = "(" ++ prettyTyN env ty ++ ")"

-- ===== Ctx, Tel, Spine =====

||| Print a context, inventing a name for each entry left-to-right, and
||| return the resulting name environment (needed by callers to print
||| whatever this context is the ambient scope for).
export
prettyCtxWithEnv : Ctx -> (String, NameEnv)
prettyCtxWithEnv [<] = ("ε", [<])
prettyCtxWithEnv (rest :< ty) =
  let (restStr, env) = prettyCtxWithEnv rest
      x = freshForTy ty env
  in (restStr ++ " ᐅ " ++ x ++ ":" ++ prettyTyN env ty, env :< x)

export
prettyCtxN : Ctx -> String
prettyCtxN ctx = fst (prettyCtxWithEnv ctx)

||| The name environment a context's own entries were invented with —
||| i.e. what to use to print anything stated *in* this context.
export
envForCtx : Ctx -> NameEnv
envForCtx ctx = snd (prettyCtxWithEnv ctx)

||| Provisional: telescope entries all resolve against the same ambient
||| env (no per-entry extension) — see docs/NovaNamedSyntax.txt's open
||| question on dependent telescopes.
export
prettyTelN : NameEnv -> Tel -> String
prettyTelN env [] = "ε"
prettyTelN env (ty :: rest) = prettyTyN env ty ++ " ◁ " ++ prettyTelN env rest

export
prettySpineN : NameEnv -> Spine -> String
prettySpineN env [] = "·"
prettySpineN env (e :: es) = prettyElemNoCommaN env e ++ go es
  where
    go : Spine -> String
    go [] = ""
    go (e' :: es') = ", " ++ prettyElemNoCommaN env e' ++ go es'

-- ===== Judgement forms =====

export
prettyCtxWfN : Ctx -> String
prettyCtxWfN ctx = "ctx-wf " ++ prettyCtxN ctx

export
prettyCtxEqN : (Ctx, Ctx) -> String
prettyCtxEqN (g0, g1) = "ctx-eq " ++ prettyCtxN g0 ++ " ≐ " ++ prettyCtxN g1

export
prettyTyWfN : (Ctx, Ty) -> String
prettyTyWfN (ctx, ty) = "ty-wf " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN (envForCtx ctx) ty

export
prettyTyEqN : (Ctx, Ty, Ty) -> String
prettyTyEqN (ctx, a, b) =
  let env = envForCtx ctx
  in "ty-eq " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN env a ++ " ≐ " ++ prettyTyN env b

export
prettySubWfN : (Sub, Ctx, Ctx) -> String
prettySubWfN (s, g, d) = "sub-wf " ++ prettySubN (envForCtx g) s ++ " : " ++ prettyCtxN g ++ " ⇒ " ++ prettyCtxN d

export
prettySubEqN : (Sub, Sub, Ctx, Ctx) -> String
prettySubEqN (s0, s1, g, d) =
  let env = envForCtx g
  in "sub-eq " ++ prettySubN env s0 ++ " ≐ " ++ prettySubN env s1 ++ " : " ++ prettyCtxN g ++ " ⇒ " ++ prettyCtxN d

export
prettySubNormWfN : (SubNorm, Ctx, Ctx) -> String
prettySubNormWfN (s, g, d) =
  "sub-norm-wf " ++ prettySubNormN (envForCtx g) s ++ " : " ++ prettyCtxN g ++ " ⇒ " ++ prettyCtxN d ++ " norm"

export
prettySubNormEqN : (SubNorm, SubNorm, Ctx, Ctx) -> String
prettySubNormEqN (s0, s1, g, d) =
  let env = envForCtx g
  in "sub-norm-eq " ++ prettySubNormN env s0 ++ " ≐ " ++ prettySubNormN env s1 ++
     " : " ++ prettyCtxN g ++ " ⇒ " ++ prettyCtxN d ++ " norm"

export
prettyElemWfN : (Ctx, Elem, Ty) -> String
prettyElemWfN (ctx, e, ty) =
  let env = envForCtx ctx
  in "el-wf " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env e ++ " : " ++ prettyTyN env ty

export
prettyElemEqN : (Ctx, Elem, Elem, Ty) -> String
prettyElemEqN (ctx, e0, e1, ty) =
  let env = envForCtx ctx
  in "el-eq " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env e0 ++ " ≐ " ++ prettyElemN env e1 ++ " : " ++ prettyTyN env ty

export
prettyTelWfN : (Ctx, Tel) -> String
prettyTelWfN (ctx, tel) = "tel-wf " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTelN (envForCtx ctx) tel

export
prettyTelEqN : (Ctx, Tel, Tel) -> String
prettyTelEqN (ctx, t0, t1) =
  let env = envForCtx ctx
  in "tel-eq " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTelN env t0 ++ " ≐ " ++ prettyTelN env t1

export
prettySpineWfN : (Ctx, Spine, Tel) -> String
prettySpineWfN (ctx, spine, tel) =
  let env = envForCtx ctx
  in "sp-wf " ++ prettyCtxN ctx ++ " ⊦ " ++ prettySpineN env spine ++ " : " ++ prettyTelN env tel

export
prettySpineEqN : (Ctx, Spine, Spine, Tel) -> String
prettySpineEqN (ctx, s0, s1, tel) =
  let env = envForCtx ctx
  in "sp-eq " ++ prettyCtxN ctx ++ " ⊦ " ++ prettySpineN env s0 ++ " ≐ " ++ prettySpineN env s1 ++ " : " ++ prettyTelN env tel

-- ===== TypingRule =====
--
-- Every context argument gets its own freshly-invented env via
-- `envForCtx`; ctx-ext's own new entry is invented the same way as any
-- other context entry (Session.idr never actually calls this to print a
-- *stored* ctx-ext line — those are kept verbatim from what the AI typed
-- — this path is only exercised for rejections/dumps of a rule value).

export
prettyTypingRuleN : TypingRule -> String
prettyTypingRuleN CtxWfEmpty =
  "ctx-emp"
prettyTypingRuleN (CtxWfExt g ty) =
  "ctx-ext " ++ prettyCtxN (g :< ty)
prettyTypingRuleN (CtxEqRefl ctx) =
  "ctx-refl " ++ prettyCtxN ctx
prettyTypingRuleN (CtxEqSym ctx0 ctx1) =
  "ctx-sym " ++ prettyCtxN ctx1 ++ " ≐ " ++ prettyCtxN ctx0
prettyTypingRuleN (CtxEqTrans ctx0 ctx1 ctx2) =
  "ctx-trans " ++ prettyCtxN ctx0 ++ " ≐ " ++ prettyCtxN ctx2 ++ " via " ++ prettyCtxN ctx1
prettyTypingRuleN (CtxWfCompute ctx alpha) =
  "ctx-cmp " ++ prettyCtxN ctx ++ " via " ++ prettyComputeRule alpha
prettyTypingRuleN (SubWfTerminal ctx) =
  "sub-term " ++ prettyCtxN ctx ++ " ⊦ ·"
prettyTypingRuleN (SubWfExt sigma e gamma delta ty) =
  let env = envForCtx gamma
  in "sub-ext " ++ prettyCtxN gamma ++ " ⊦ " ++ prettySubN env (Ext sigma e) ++ " to " ++ prettyCtxN (delta :< ty)
prettyTypingRuleN (SubEqRefl s g d) =
  "sub-refl " ++ prettyCtxN g ++ " ⊦ " ++ prettySubN (envForCtx g) s ++ " : " ++ prettyCtxN d
prettyTypingRuleN (SubEqSym s0 s1 g d) =
  let env = envForCtx g
  in "sub-sym " ++ prettyCtxN g ++ " ⊦ " ++ prettySubN env s1 ++ " ≐ " ++ prettySubN env s0 ++ " : " ++ prettyCtxN d
prettyTypingRuleN (SubEqTrans s0 s1 s2 g d) =
  let env = envForCtx g
  in "sub-trans " ++ prettyCtxN g ++ " ⊦ " ++ prettySubN env s0 ++ " ≐ " ++ prettySubN env s2 ++
     " : " ++ prettyCtxN d ++ " via " ++ prettySubN env s1
prettyTypingRuleN (SubNormWfTerminal ctx) =
  "sub-norm-term " ++ prettyCtxN ctx ++ " ⊦ ·"
prettyTypingRuleN (SubNormWfExt sigma e gamma delta ty) =
  let env = envForCtx gamma
  in "sub-norm-ext " ++ prettyCtxN gamma ++ " ⊦ " ++ prettySubNormN env (sigma :< e) ++ " to " ++ prettyCtxN (delta :< ty)
prettyTypingRuleN (SubNormEqRefl s g d) =
  "sub-norm-refl " ++ prettyCtxN g ++ " ⊦ " ++ prettySubNormN (envForCtx g) s ++ " : " ++ prettyCtxN d
prettyTypingRuleN (SubNormEqSym s0 s1 g d) =
  let env = envForCtx g
  in "sub-norm-sym " ++ prettyCtxN g ++ " ⊦ " ++ prettySubNormN env s1 ++ " ≐ " ++ prettySubNormN env s0 ++ " : " ++ prettyCtxN d
prettyTypingRuleN (SubNormEqTrans s0 s1 s2 g d) =
  let env = envForCtx g
  in "sub-norm-trans " ++ prettyCtxN g ++ " ⊦ " ++ prettySubNormN env s0 ++ " ≐ " ++ prettySubNormN env s2 ++
     " : " ++ prettyCtxN d ++ " via " ++ prettySubNormN env s1
prettyTypingRuleN (SubNormEqExt s0 s1 t0 t1 gamma0 gamma1 ty) =
  let env = envForCtx gamma0
  in "sub-norm-ext-eq " ++ prettyCtxN gamma0 ++ " ⊦ " ++ prettySubNormN env (s0 :< t0) ++ " ≐ " ++ prettySubNormN env (s1 :< t1) ++
     " : " ++ prettyCtxN (gamma1 :< ty)
prettyTypingRuleN (TyWfZero ctx) =
  "ty-zero " ++ prettyCtxN ctx ++ " ⊦ 𝟘"
prettyTypingRuleN (TyWfOne ctx) =
  "ty-one " ++ prettyCtxN ctx ++ " ⊦ 𝟙"
prettyTypingRuleN (TyWfNat ctx) =
  "ty-nat " ++ prettyCtxN ctx ++ " ⊦ ℕ"
prettyTypingRuleN (TyWfUniverse ctx) =
  "ty-univ " ++ prettyCtxN ctx ++ " ⊦ 𝕌"
prettyTypingRuleN (TyWfPi ctx a b) =
  "ty-pi " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN (envForCtx ctx) (PiTy a b)
prettyTypingRuleN (TyWfSigma ctx a b) =
  "ty-sigma " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN (envForCtx ctx) (SigmaTy a b)
prettyTypingRuleN (TyWfEq ctx l r ty) =
  "ty-eq-form " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN (envForCtx ctx) (EqTy l r ty)
prettyTypingRuleN (TyWfEl ctx e) =
  "ty-el " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN (envForCtx ctx) (El e)
prettyTypingRuleN (TyWfQuotient ctx a r) =
  "ty-quotient " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN (envForCtx ctx) (Quotient a r)
prettyTypingRuleN (TyWfCompute ctx alpha ty beta) =
  "ty-cmp " ++ prettyCtxN ctx ++ " via " ++ prettyComputeRule alpha ++
  " ⊦ " ++ prettyTyN (envForCtx ctx) ty ++ " via " ++ prettyComputeRule beta
prettyTypingRuleN (TyEqRefl ctx ty) =
  "ty-refl " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN (envForCtx ctx) ty
prettyTypingRuleN (TyEqSym ctx ty0 ty1) =
  let env = envForCtx ctx
  in "ty-sym " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN env ty1 ++ " ≐ " ++ prettyTyN env ty0
prettyTypingRuleN (TyEqTrans ctx ty0 ty1 ty2) =
  let env = envForCtx ctx
  in "ty-trans " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN env ty0 ++ " ≐ " ++ prettyTyN env ty2 ++ " via " ++ prettyTyN env ty1
prettyTypingRuleN (TyEqCongEqTy ctx a0 b0 ty0 a1 b1 ty1) =
  let env = envForCtx ctx
  in "ty-eq-cong " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN env (EqTy a0 b0 ty0) ++ " ≐ " ++ prettyTyN env (EqTy a1 b1 ty1)
prettyTypingRuleN (TyEqCongEl ctx t0 t1) =
  let env = envForCtx ctx
  in "ty-el-cong " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTyN env (El t0) ++ " ≐ " ++ prettyTyN env (El t1)
prettyTypingRuleN (TyWfSubst gamma0 gamma1 sigma a) =
  "ty-wf-subst " ++ prettyCtxN gamma0 ++ " ⊦ " ++ prettySubN (envForCtx gamma0) sigma ++
  " to " ++ prettyCtxN gamma1 ++ " ⊦ " ++ prettyTyN (envForCtx gamma1) a
prettyTypingRuleN (TyEqSubst gamma0 gamma1 sigma0 sigma1 a0 a1) =
  let env1 = envForCtx gamma1
  in "ty-eq-subst " ++ prettyCtxN gamma0 ++ " ⊦ " ++ prettySubN (envForCtx gamma0) sigma0 ++ " ≐ " ++ prettySubN (envForCtx gamma0) sigma1 ++
     " to " ++ prettyCtxN gamma1 ++ " ⊦ " ++ prettyTyN env1 a0 ++ " ≐ " ++ prettyTyN env1 a1
prettyTypingRuleN (ElemWfVar g n) =
  "el-var " ++ prettyCtxN g ++ " ⊦ " ++ nameAt (envForCtx g) n
prettyTypingRuleN (ElemWfOneIntro ctx) =
  "el-one " ++ prettyCtxN ctx ++ " ⊦ ()"
prettyTypingRuleN (ElemWfZeroIntro ctx) =
  "el-zero " ++ prettyCtxN ctx ++ " ⊦ Z"
prettyTypingRuleN (ElemWfSucIntro ctx e) =
  "el-suc " ++ prettyCtxN ctx ++ " ⊦ S " ++ prettyElemAtomN (envForCtx ctx) e
prettyTypingRuleN (ElemWfPiIntro ctx f a b) =
  let env = envForCtx ctx
  in "el-pi-i " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env (PiIntro f) ++ " : " ++ prettyTyN env (PiTy a b)
prettyTypingRuleN (ElemWfPiApp gamma f a b e) =
  let env = envForCtx gamma
  in "el-pi-e " ++ prettyCtxN gamma ++ " ⊦ (" ++ prettyElemN env f ++ " : " ++ prettyTyN env (PiTy a b) ++ ") " ++ prettyElemAtomN env e
prettyTypingRuleN (ElemWfSigmaIntro ctx u v a b) =
  let env = envForCtx ctx
  in "el-sigma-i " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env (SigmaIntro u v) ++ " : " ++ prettyTyN env (SigmaTy a b)
prettyTypingRuleN (ElemWfSigmaElim1 ctx e a b) =
  let env = envForCtx ctx
  in "el-sigma-e1 " ++ prettyCtxN ctx ++ " ⊦ (" ++ prettyElemN env e ++ " : " ++ prettyTyN env (SigmaTy a b) ++ ") .π₁"
prettyTypingRuleN (ElemWfSigmaElim2 ctx e a b) =
  let env = envForCtx ctx
  in "el-sigma-e2 " ++ prettyCtxN ctx ++ " ⊦ (" ++ prettyElemN env e ++ " : " ++ prettyTyN env (SigmaTy a b) ++ ") .π₂"
prettyTypingRuleN (ElemWfZeroElim ctx e ty) =
  let env = envForCtx ctx
  in "el-zero-e " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env (ZeroElim e) ++ " : " ++ prettyTyN env ty
prettyTypingRuleN (ElemWfNatElim ctx z s t ty) =
  let env = envForCtx ctx
      n  = freshFromList candidatesNat env
      ih = freshIH (env :< n)
  in "el-nat-e " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env (NatElim z s t) ++
     " motive (" ++ n ++ " " ++ ih ++ ". " ++ prettyTyN (env :< n :< ih) ty ++ ")"
prettyTypingRuleN (ElemWfClass ctx a ty r) =
  let env = envForCtx ctx
  in "el-class " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env (Class a) ++ " : " ++ prettyTyN env (Quotient ty r)
prettyTypingRuleN (ElemWfQuotElim ctx ty r motive f q) =
  let env = envForCtx ctx
      qn  = freshGeneric env
  in "el-quot-elim " ++ prettyCtxN ctx ++ " ⊦ quot-elim " ++ prettyElemAtomN env f ++
     " (" ++ prettyElemN env q ++ " : " ++ prettyTyN env (Quotient ty r) ++ ") motive (" ++ qn ++ ". " ++ prettyTyN (env :< qn) motive ++ ")"
prettyTypingRuleN (ElemWfSubst gamma0 gamma1 sigma t a) =
  let env1 = envForCtx gamma1
  in "el-wf-subst " ++ prettyCtxN gamma0 ++ " ⊦ " ++ prettySubN (envForCtx gamma0) sigma ++
     " to " ++ prettyCtxN gamma1 ++ " ⊦ " ++ prettyElemN env1 t ++ " : " ++ prettyTyN env1 a
prettyTypingRuleN (ElemEqReflection ctx a a0 a1 ty) =
  let env = envForCtx ctx
  in "el-reflect " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env a ++ " : (" ++ prettyTyN env (EqTy a0 a1 ty) ++ ") reflect"
prettyTypingRuleN (ElemEqCongSuc ctx t0 t1) =
  let env = envForCtx ctx
  in "el-suc-cong " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env (NatIntro1 t0) ++ " ≐ " ++ prettyElemN env (NatIntro1 t1)
prettyTypingRuleN (ElemEqCongPiApp ctx f0 f1 a b a0 a1) =
  let env = envForCtx ctx
  in "el-app-cong " ++ prettyCtxN ctx ++ " ⊦ (" ++ prettyElemN env f0 ++ " ≐ " ++ prettyElemN env f1 ++ " : " ++ prettyTyN env (PiTy a b) ++ ") " ++
     prettyElemAtomN env a0 ++ " ≐ " ++ prettyElemAtomN env a1
prettyTypingRuleN (ElemEqCongClass ctx ty r a0 a1) =
  let env = envForCtx ctx
  in "el-class-cong " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env (Class a0) ++ " ≐ " ++ prettyElemN env (Class a1) ++ " : " ++ prettyTyN env (Quotient ty r)
prettyTypingRuleN (ElemEqQuotient ctx ty r a b witness) =
  let env = envForCtx ctx
  in "el-quot-eq " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env (Class a) ++ " ≐ " ++ prettyElemN env (Class b) ++
     " : " ++ prettyTyN env (Quotient ty r) ++ " via " ++ prettyElemN env witness
prettyTypingRuleN (ElemEqSubst gamma0 gamma1 sigma0 sigma1 t0 t1 a) =
  let env1 = envForCtx gamma1
  in "el-eq-subst " ++ prettyCtxN gamma0 ++ " ⊦ " ++ prettySubN (envForCtx gamma0) sigma0 ++ " ≐ " ++ prettySubN (envForCtx gamma0) sigma1 ++
     " to " ++ prettyCtxN gamma1 ++ " ⊦ " ++ prettyElemN env1 t0 ++ " ≐ " ++ prettyElemN env1 t1 ++ " : " ++ prettyTyN env1 a
prettyTypingRuleN (ElemWfRefl ctx e ty) =
  let env = envForCtx ctx
  in "el-refl " ++ prettyCtxN ctx ++ " ⊦ Refl : " ++ prettyElemAtomN env e ++ " ∈ " ++ prettyTyN env ty
prettyTypingRuleN (ElemEqTyCoe ctx a b ty0 ty1) =
  let env = envForCtx ctx
  in "el-ty-coe-eq " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env a ++ " ≐ " ++ prettyElemN env b ++ " : " ++ prettyTyN env ty0 ++ " ↝ " ++ prettyTyN env ty1
prettyTypingRuleN (ElemWfTyCoe ctx e ty0 ty1) =
  let env = envForCtx ctx
  in "el-ty-coe " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env e ++ " : " ++ prettyTyN env ty0 ++ " ↝ " ++ prettyTyN env ty1
prettyTypingRuleN (ElemWfCtxCoe ctx0 ctx1 e ty) =
  let env1 = envForCtx ctx1
  in "el-ctx-coe " ++ prettyCtxN ctx0 ++ " ≐ " ++ prettyCtxN ctx1 ++ " ⊦ " ++ prettyElemN env1 e ++ " : " ++ prettyTyN env1 ty
prettyTypingRuleN (ElemWfZeroTy ctx) =
  "el-zero-ty " ++ prettyCtxN ctx ++ " ⊦ 𝟘 : 𝕌"
prettyTypingRuleN (ElemWfOneTy ctx) =
  "el-one-ty " ++ prettyCtxN ctx ++ " ⊦ 𝟙 : 𝕌"
prettyTypingRuleN (ElemWfNatTy ctx) =
  "el-nat-ty " ++ prettyCtxN ctx ++ " ⊦ ℕ : 𝕌"
prettyTypingRuleN (ElemWfPiTy ctx a b) =
  "el-pi-ty " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN (envForCtx ctx) (Elem.PiTy a b) ++ " : 𝕌"
prettyTypingRuleN (ElemWfSigmaTy ctx a b) =
  "el-sigma-ty " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN (envForCtx ctx) (Elem.SigmaTy a b) ++ " : 𝕌"
prettyTypingRuleN (ElemWfEqTy ctx l r ty) =
  "el-eq-ty " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN (envForCtx ctx) (Elem.EqTy l r ty) ++ " : 𝕌"
prettyTypingRuleN (ElemWfCompute ctx alpha e beta ty gamma) =
  let env = envForCtx ctx
  in "el-cmp " ++ prettyCtxN ctx ++ " via " ++ prettyComputeRule alpha ++
     " ⊦ " ++ prettyElemN env e ++ " via " ++ prettyComputeRule beta ++
     " : " ++ prettyTyN env ty ++ " via " ++ prettyComputeRule gamma
prettyTypingRuleN (ElemEqSigVar ctx sigma x) =
  "sig-var-eq " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemAtomN (envForCtx ctx) (SigVar x sigma)
prettyTypingRuleN (ElemWfSigVar ctx sigma x) =
  "sig-var " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemAtomN (envForCtx ctx) (SigVar x sigma)
prettyTypingRuleN (SigExt gamma x a ty) =
  let env = envForCtx gamma
  in "sig " ++ prettyCtxN gamma ++ " ⊦ " ++ x ++ " ≔ " ++ prettyElemN env a ++ " : " ++ prettyTyN env ty
prettyTypingRuleN (ElemEqRefl ctx e ty) =
  let env = envForCtx ctx
  in "el-eq-refl " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env e ++ " : " ++ prettyTyN env ty
prettyTypingRuleN (ElemEqSym ctx e0 e1 ty) =
  let env = envForCtx ctx
  in "el-eq-sym " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env e1 ++ " ≐ " ++ prettyElemN env e0 ++ " : " ++ prettyTyN env ty
prettyTypingRuleN (ElemEqTrans ctx e0 e1 e2 ty) =
  let env = envForCtx ctx
  in "el-eq-trans " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyElemN env e0 ++ " ≐ " ++ prettyElemN env e2 ++
     " : " ++ prettyTyN env ty ++ " via " ++ prettyElemN env e1
prettyTypingRuleN (TelEqRefl ctx tel) =
  "tel-refl " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTelN (envForCtx ctx) tel
prettyTypingRuleN (TelEqSym ctx tel0 tel1) =
  let env = envForCtx ctx
  in "tel-sym " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTelN env tel1 ++ " ≐ " ++ prettyTelN env tel0
prettyTypingRuleN (TelEqTrans ctx tel0 tel1 tel2) =
  let env = envForCtx ctx
  in "tel-trans " ++ prettyCtxN ctx ++ " ⊦ " ++ prettyTelN env tel0 ++ " ≐ " ++ prettyTelN env tel2 ++ " via " ++ prettyTelN env tel1
prettyTypingRuleN (SpineEqRefl ctx spine tel) =
  let env = envForCtx ctx
  in "sp-refl " ++ prettyCtxN ctx ++ " ⊦ " ++ prettySpineN env spine ++ " : " ++ prettyTelN env tel
prettyTypingRuleN (SpineEqSym ctx s0 s1 tel) =
  let env = envForCtx ctx
  in "sp-sym " ++ prettyCtxN ctx ++ " ⊦ " ++ prettySpineN env s1 ++ " ≐ " ++ prettySpineN env s0 ++ " : " ++ prettyTelN env tel
prettyTypingRuleN (SpineEqTrans ctx s0 s1 s2 tel) =
  let env = envForCtx ctx
  in "sp-trans " ++ prettyCtxN ctx ++ " ⊦ " ++ prettySpineN env s0 ++ " ≐ " ++ prettySpineN env s2 ++ " : " ++ prettyTelN env tel ++ " via " ++ prettySpineN env s1

export
prettyJudgementFormN : JudgementForm -> String
prettyJudgementFormN (JfCtxWf ctx)       = prettyCtxWfN ctx
prettyJudgementFormN (JfCtxEq p)         = prettyCtxEqN p
prettyJudgementFormN (JfTyWf p)          = prettyTyWfN p
prettyJudgementFormN (JfTyEq p)          = prettyTyEqN p
prettyJudgementFormN (JfSubWf p)         = prettySubWfN p
prettyJudgementFormN (JfSubEq p)         = prettySubEqN p
prettyJudgementFormN (JfSubNormWf p)     = prettySubNormWfN p
prettyJudgementFormN (JfSubNormEq p)     = prettySubNormEqN p
prettyJudgementFormN (JfElemWf p)        = prettyElemWfN p
prettyJudgementFormN (JfElemEq p)        = prettyElemEqN p
prettyJudgementFormN (JfTelWf p)         = prettyTelWfN p
prettyJudgementFormN (JfTelEq p)         = prettyTelEqN p
prettyJudgementFormN (JfSpineWf p)       = prettySpineWfN p
prettyJudgementFormN (JfSpineEq p)       = prettySpineEqN p
