module Nova.Foundation.Derivation.NamedParser

-- Named surface syntax parser (see docs/NovaNamedSyntax.txt).
--
-- This parser produces exactly the same core, de Bruijn-indexed AST
-- (Ty/Elem/Ctx/TypingRule/JudgementForm from Nova.Foundation.Syntax and
-- Nova.Foundation.Derivation) that Nova.Foundation.Parser and
-- Nova.Foundation.Derivation.Parser already produce from the indexed
-- (☐ₙ) surface syntax — there is no separate "named" AST here. Instead,
-- every parsing function threads an explicit `NameEnv`, a list of names
-- parallel to the `Ctx`/telescope being built, and resolves a variable
-- reference to a de Bruijn index by looking up its position in that list
-- (innermost/rightmost binder wins — ordinary lexical shadowing).
--
-- Two different things get a name, for two different reasons (see the
-- header of docs/NovaNamedSyntax.txt for the full rationale):
--   1. `ctx-ext`/`el-var` — parseNamedCtx assigns a name to every `Γ ᐅ x:T`
--      entry it parses, and el-var resolves a name back to an index via
--      `resolveName`.
--   2. Wrapping constructs (`→`, `⨯`, `/`, `λ`, `ℕ-elim`'s step branch,
--      `el-quot-elim`'s motive) carry their bound name(s) inline in their
--      own surface syntax, because once wrapped, that variable is popped
--      out of the tracked Γ into an anonymous compiled-in binder slot —
--      see the design doc for why this is required for self-contained
--      values (`.target` files, `sig`/`dump` echoes) that have no
--      accompanying `ctx-ext` trail to fall back on.
--
-- `sub-id`/`sub-wk`/`sub-chn`/`sub-norm-chn`/`sub-norm-eq-chn` (identity,
-- weakening, and composition construction for substitutions) don't exist
-- in this grammar at all — every Sub actually needed by this codebase's
-- derivations is an explicit, flat extension list (`· | σ, t`), exactly
-- like SubNorm's own grammar (see `parseSub`, and NovaNamedSyntax.txt).
-- This also means this parser never needs lookahead: every context a
-- rule references is written out in full before anything that needs its
-- names.

import Data.SnocList

import Me.Russoul.Text.Lexer.Token
import Me.Russoul.Text.Lexer
import Me.Russoul.Text.Parser
import Me.Russoul.Text.Parser.OverToken
import Me.Russoul.Text.Position
import Me.Russoul.Text.Range

import Nova.Foundation.Syntax
import Nova.Foundation.Parser
import Nova.Foundation.Derivation
import Nova.Foundation.Derivation.Parser

%default covering

-- Optional whitespace between tokens (Nova.Foundation.Parser.sp is private
-- to that module, so this is its own local copy).
sp : Rule ()
sp = optSpace

-- ===== Name environment =====

||| One name per context entry, in the same order/length as a `Ctx`
||| (rightmost = innermost = de Bruijn index 0).
public export
NameEnv : Type
NameEnv = SnocList String

||| The wildcard/anonymous name. Never resolvable — deliberately so, since
||| a context may legally contain more than one `_` entry (each one
||| shadowing nothing, referring to nothing).
export
wildcard : String
wildcard = "_"

||| Resolve a name to a de Bruijn index against a name environment.
||| Innermost (rightmost) binder of that name wins — ordinary lexical
||| shadowing. `"_"` never resolves.
export
resolveName : NameEnv -> String -> Maybe Nat
resolveName [<] x = Nothing
resolveName (env :< y) x =
  if x /= wildcard && y == x
    then Just 0
    else map S (resolveName env x)

-- ===== Local identifiers =====
--
-- Distinct from Nova.Foundation.Parser.parseSigIdentifier (which lexes
-- *signature* identifiers, always followed by `[...]` and therefore never
-- ambiguous with a local name). Local identifiers additionally allow `'`
-- in the continuation (but not as the first character), matching common
-- mathematical convention (`n'`, `ih'`, ...).
--
-- Known limitation (inherited from the rest of this parser, not
-- introduced here): a local variable literally spelled the same as a
-- reserved keyword token that can match with nothing required afterward
-- (`Z`, `Refl`, and prefix-of-keyword names like `Sn`, `classify`,
-- `Elem` immediately followed by more identifier characters with no
-- separating whitespace) can be misparsed, exactly as an equally-named
-- signature identifier already could be in the unnamed parser. Avoid
-- naming a local variable exactly `Z`/`Refl`/`S`/`El`/`class` or a prefix
-- of `𝟘-elim`/`ℕ-elim`/`quot-elim` immediately followed by more
-- identifier characters.
export covering
parseLocalIdentifier : Rule String
parseLocalIdentifier = do
  c  <- terminal "identifier start" $ \tok =>
          case tok of
            Symbol ch => if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch == '_'
                         then Just ch
                         else Nothing
            _ => Nothing
  cs <- many (terminal "identifier char" $ \tok =>
          case tok of
            Symbol ch => if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
                            (ch >= '0' && ch <= '9') || ch == '_' || ch == '\''
                         then Just ch
                         else Nothing
            _ => Nothing)
  let name = pack (c :: cs)
  guard "Reserved keyword" (name /= "via" && name /= "to" && name /= "motive" &&
                            name /= "reflect" && name /= "norm")
  pure name

-- ===== Block 1: Sub and Elem parsers (mutually recursive) =====
--
-- Mirrors Nova.Foundation.Parser's Block 1 exactly, except every function
-- takes an explicit NameEnv and:
--   - a bare identifier (t{5}) resolves against it instead of parsing ☐ₙ;
--   - λ (t{2}) and ℕ-elim's step branch (t{2}) carry inline binder
--     name(s), extending the env for their own body only;
--   - the Pi/Sigma-as-universe-code infix forms (t{1}) gain an inline
--     domain name, `(x:A) → B` / `(x:A) ⨯ B`, with `A → B`/`A ⨯ B` as
--     sugar for `(_:A) → B`/`(_:A) ⨯ B`.

mutual
  -- σ, e₁, e₂   (left-assoc Ext)
  -- (nothing)    (Terminal — the empty substitution is written as
  --              literally no text at all; "·" is not valid syntax here)
  -- e₁, e₂       (a non-empty substitution is a bare comma-separated
  --              element list, with no leading marker)
  --
  -- No id/↑/∘: every substitution actually used in this codebase's
  -- derivations is written as an explicit, flat extension list, exactly
  -- like SubNorm's own grammar — see NovaNamedSyntax.txt. Id/Wk/Chain
  -- still exist on the core Sub type (used internally, e.g. for
  -- quotient-type formation's `A[↑]`) — they're just not
  -- surface-syntax-constructible via a dedicated sub-id/sub-wk/sub-chn
  -- rule anymore. e is resolved against `env`, the substitution's
  -- *domain* context.
  export covering
  parseSub : NameEnv -> Rule Sub
  parseSub env = do
    first <- optional (parseElemNoComma env)
    case first of
      Nothing => pure Terminal
      Just e  => do
        rest <- many (do sp; char_ ','; sp; e' <- parseElemNoComma env; pure e')
        pure (foldl Ext Terminal (e :: rest))

  -- e₁ , e₂          (right-assoc SigmaIntro)
  -- (x:e) → e'       (right-assoc PiTy element, NAMED — sugar: e → e' for (_:e) → e')
  -- (x:e) ⨯ e'       (right-assoc SigmaTy element, NAMED — sugar likewise)
  -- e₀ ≡ e₁ ∈ e₂     (EqTy element)
  -- λx. e            (PiIntro, NAMED)
  -- S e               (NatIntro1)
  -- 𝟘-elim e          (ZeroElim)
  -- ℕ-elim z (n ih. s) t  (NatElim, NAMED — n/ih may each be `_`)
  -- class e           (Class)
  -- quot-elim f q     (QuotElim)
  -- e @               (PiElim)
  -- e .π₁             (SigmaElim1)
  -- e .π₂             (SigmaElim2)
  -- x                 (CtxVar, resolved by name)
  -- ()                (OneIntro)
  -- Z                 (NatIntro0)
  -- Refl              (Refl)
  -- 𝟘 𝟙 ℕ            (universe codes ZeroTy OneTy NatTy)
  -- x[t˲]             (SigVar)
  export covering
  parseElem : NameEnv -> Rule Elem
  parseElem env = do
    e <- parseElemNoComma env
    (do sp; char_ ','; sp; e' <- parseElem env; pure (SigmaIntro e e'))
      <|> pure e

  -- Element without top-level comma, used inside Sub.Ext and Spine
  -- to avoid ambiguity with SigmaIntro's comma.
  covering
  parseElemNoComma : NameEnv -> Rule Elem
  parseElemNoComma env =
        -- Named Pi/Sigma domain group: (x:A) → B  or  (x:A) ⨯ B
        (do char_ '('; sp; x <- parseLocalIdentifier; sp; char_ ':'; sp
            a <- parseElem env; sp; char_ ')'; sp
            (do str_ "→"; sp; b <- parseElemNoComma (env :< x); pure (Elem.PiTy a b))
              <|> (do str_ "⨯"; sp; b <- parseElemNoComma (env :< x); pure (Elem.SigmaTy a b)))
    <|> (do e <- parseElemPrefix env
            (do sp; str_ "→"; sp; e' <- parseElemNoComma (env :< wildcard); pure (Elem.PiTy e e'))
              <|> (do sp; str_ "⨯"; sp; e' <- parseElemNoComma (env :< wildcard); pure (Elem.SigmaTy e e'))
              <|> (do sp; str_ "≡"; sp
                      e1 <- parseElemPrefix env; sp; str_ "∈"; sp
                      e2 <- parseElemPrefix env
                      pure (Elem.EqTy e e1 e2))
              <|> pure e)

  -- Prefix operators: take an atomic argument
  covering
  parseElemPrefix : NameEnv -> Rule Elem
  parseElemPrefix env =
        (do str_ "λ"; sp; x <- parseLocalIdentifier; sp; char_ '.'; sp
            e <- parseElemPostfix (env :< x); pure (PiIntro e))
    <|> (do str_ "𝟘-elim"; space; e <- parseElemAtom env; pure (ZeroElim e))
    <|> (do str_ "ℕ-elim"; space
            z <- parseElemAtom env; space
            char_ '('; sp; n <- parseLocalIdentifier; space; ih <- parseLocalIdentifier
            sp; char_ '.'; sp; s <- parseElemAtom (env :< n :< ih); sp; char_ ')'; space
            t <- parseElemAtom env
            pure (NatElim z s t))
    <|> (do str_ "S"; space; e <- parseElemAtom env; pure (NatIntro1 e))
    <|> (do str_ "class"; space; e <- parseElemAtom env; pure (Class e))
    <|> (do str_ "quot-elim"; space
            char_ '('; sp; a <- parseLocalIdentifier; sp; char_ '.'; sp
            f <- parseElem (env :< a); sp; char_ ')'; space
            q <- parseElemAtom env
            pure (QuotElim f q))
    <|> parseElemPostfix env

  -- Level 3: PiApp and projections (t t, t .π₁, t .π₂, left-assoc)
  -- Argument of application is an atom.
  covering
  parseElemPostfix : NameEnv -> Rule Elem
  parseElemPostfix env = do
    e <- parseElemAtom env
    parseElemPostfixCont env e

  covering
  parseElemPostfixCont : NameEnv -> Elem -> Rule Elem
  parseElemPostfixCont env e =
        (do sp; str_ ".π₁"; parseElemPostfixCont env (SigmaElim1 e))
    <|> (do sp; str_ ".π₂"; parseElemPostfixCont env (SigmaElim2 e))
    <|> (do sp; e' <- parseElemAtom env; parseElemPostfixCont env (PiApp e e'))
    <|> pure e

  -- t˲ ::= (nothing) | t˲ , t   (normal substitution, resolved against `env`,
  -- the substitution's *usage* context): the empty substitution is written
  -- as literally no text at all; "·" is not valid syntax here. A non-empty
  -- substitution is a bare comma-separated element list — exactly like
  -- parseSub, just building a SubNorm instead of a Sub.
  export covering
  parseSubNorm : NameEnv -> Rule SubNorm
  parseSubNorm env = do
    first <- optional (parseElemNoComma env)
    case first of
      Nothing => pure [<]
      Just e  => do
        rest <- many (do sp; char_ ','; sp; e' <- parseElemNoComma env; pure e')
        pure (foldl (:<) [<] (e :: rest))

  -- Atomic elements: constants, a local variable (resolved by name), a
  -- signature reference, or a parenthesised expression.
  -- After '(' peek for ')' to distinguish () = OneIntro from (e).
  export covering
  parseElemAtom : NameEnv -> Rule Elem
  parseElemAtom env =
        (do char_ '('
            sp
            unit <- optional (char_ ')')
            case unit of
              Just _  => pure OneIntro
              Nothing => do e <- parseElem env; sp; char_ ')'; pure e)
    <|> (str_ "Refl" $> Refl)
    <|> (str_ "Z"    $> NatIntro0)
    <|> (str_ "𝟘"   $> Elem.ZeroTy)
    <|> (str_ "𝟙"   $> Elem.OneTy)
    <|> (str_ "ℕ"   $> Elem.NatTy)
    <|> (do x <- parseLocalIdentifier
            (do sp; char_ '['; sp; es <- parseSubNorm env; sp; char_ ']'
                pure (SigVar x es))
              <|> (case resolveName env x of
                     Just n  => pure (CtxVar n)
                     Nothing => fail "unbound identifier '\{x}'"))

-- ===== Block 2: Ty parsers =====
--
-- Mirrors Nova.Foundation.Parser's Block 2, with the Pi/Sigma/Quotient
-- type formers (T{1}) gaining inline binder name(s):
--   (x:A) → B     sugar: A → B  ≡  (_:A) → B
--   (x:A) ⨯ B     sugar: A ⨯ B  ≡  (_:A) ⨯ B
--   A / (x y. R)  sugar: A / R  ≡  A / (_ _. R)

mutual
  -- e₀ ≡ e₁ ∈ A      (EqTy:  two Elem args + Ty)
  -- (x:A) → B         (PiTy, NAMED)
  -- (x:A) ⨯ B         (SigmaTy, NAMED)
  -- A / (x y. R)      (Quotient, NAMED)
  -- El e              (El, e is an Elem atom)
  -- 𝟘 𝟙 ℕ 𝕌          (constant types)
  export covering
  parseTy : NameEnv -> Rule Ty
  parseTy env =
        (do e0 <- parseElemPrefix env; sp
            str_ "≡"; sp
            e1 <- parseElemPrefix env; sp
            str_ "∈"; sp
            a  <- parseTyArrow env
            pure (Ty.EqTy e0 e1 a))
    <|> parseTyArrow env

  -- (x:A) → B  or  (x:A) ⨯ B  or  A / (x y. R)  (right-associative infix)
  covering
  parseTyArrow : NameEnv -> Rule Ty
  parseTyArrow env =
        -- Named Pi/Sigma domain group: (x:A) → B  or  (x:A) ⨯ B
        (do char_ '('; sp; x <- parseLocalIdentifier; sp; char_ ':'; sp
            a <- parseTy env; sp; char_ ')'; sp
            (do str_ "→"; sp; b <- parseTyArrow (env :< x); pure (Ty.PiTy a b))
              <|> (do str_ "⨯"; sp; b <- parseTyArrow (env :< x); pure (Ty.SigmaTy a b)))
    <|> (do a <- parseTyEl env
            (do sp; str_ "→"; sp; b <- parseTyArrow (env :< wildcard); pure (Ty.PiTy a b))
              <|> (do sp; str_ "⨯"; sp; b <- parseTyArrow (env :< wildcard); pure (Ty.SigmaTy a b))
              <|> (do sp; str_ "/"; sp; r <- parseQuotientRelation env; pure (Ty.Quotient a r))
              <|> pure a)
   where
    -- (x y. R)  or, as sugar, bare R ≡ (_ _. R)
    covering
    parseQuotientRelation : NameEnv -> Rule Ty
    parseQuotientRelation env =
          (do char_ '('; sp; x <- parseLocalIdentifier; space; y <- parseLocalIdentifier
              sp; char_ '.'; sp; r <- parseTyArrow (env :< x :< y); sp; char_ ')'
              pure r)
      <|> parseTyArrow (env :< wildcard :< wildcard)

  -- El e  (prefix El, e is an Elem atom)
  covering
  parseTyEl : NameEnv -> Rule Ty
  parseTyEl env =
        (do str_ "El"; space; e <- parseElemAtom env; pure (El e))
    <|> parseTyAtom env

  -- Constant types and parenthesised type
  covering
  parseTyAtom : NameEnv -> Rule Ty
  parseTyAtom env =
        (str_ "𝟘" $> Ty.ZeroTy)
    <|> (str_ "𝟙" $> Ty.OneTy)
    <|> (str_ "ℕ" $> Ty.NatTy)
    <|> (str_ "𝕌" $> Ty.UniverseTy)
    <|> inParen (parseTy env)

-- ===== Ctx, Tel, Spine =====

-- Γ ::= ε | Γ ᐅ x:A   (snoc list, left-associative, NAMED)
-- Every entry names the variable it introduces (sugar: a bare `A`, with
-- no `x:`, defaults to `_` — useful when re-stating an already-built
-- context whose entries aren't referenced by name in the current rule).
-- Self-contained: parses a full Γ from `ε`, producing both the core `Ctx`
-- and its parallel `NameEnv` — nothing needs to be threaded in from
-- outside, since every Γ is always written out in full at every use site
-- (exactly as in the unnamed parser).
export covering
parseNamedCtx : Rule (Ctx, NameEnv)
parseNamedCtx = do
  str_ "ε"
  parseNamedCtxFrom [<] [<]
 where
  covering
  parseNamedCtxFrom : Ctx -> NameEnv -> Rule (Ctx, NameEnv)
  parseNamedCtxFrom ctx env =
        (do sp; str_ "ᐅ"; sp
            (do x <- parseLocalIdentifier; sp; char_ ':'; sp
                ty <- parseTy env
                parseNamedCtxFrom (ctx :< ty) (env :< x))
              <|> (do ty <- parseTy env
                      parseNamedCtxFrom (ctx :< ty) (env :< wildcard)))
    <|> pure (ctx, env)

-- Δ ::= ε | A ◁ Δ   (list, right-associative)
--
-- Provisional: entries are all resolved against the *same* ambient `env`
-- (no per-entry extension) — see docs/NovaNamedSyntax.txt's open question
-- on whether a dependent telescope needs its own nested name scope. None
-- of the worked derivations exercise tel-wf/sp-wf, so this is untested.
export covering
parseTel : NameEnv -> Rule Tel
parseTel env =
      (str_ "ε" $> [])
  <|> (do a <- parseTy env
          sp; str_ "◁"; sp
          rest <- parseTel env
          pure (a :: rest))

-- ē ::= · | e₁, ..., eₙ   (comma-separated, no trailing ·)
export covering
parseSpine : NameEnv -> Rule Spine
parseSpine env =
      (str_ "·" $> [])
  <|> (do e    <- parseElemNoComma env
          rest <- many (do sp; char_ ','; sp; parseElemNoComma env)
          pure (e :: rest))

-- ===== TypingRule parser =====
-- Keyword-first: each rule starts with a unique keyword. Mirrors
-- Nova.Foundation.Derivation.Parser.parseNamedTypingRule rule-for-rule; the
-- compute-rule parser (α) is reused entirely unchanged (it only ever
-- navigates inside an already-named term, never introduces a binder).
--
-- Where a rule involves more than one context (Γ₀/Γ₁, Γ/Δ, Γ/Δ/Θ, ...),
-- each Ty/Elem/Sub/SubNorm argument is resolved against whichever context
-- it lives in per the rule's premises (see the cheat sheet and
-- NovaFoundation.txt), not necessarily the first context parsed. Every
-- such context is written *before* the first thing that needs its names
-- — including in `sub-chn`/`sub-norm-chn`/`sub-norm-eq-chn`, whose surface
-- syntax states the domain-defining substitution (with its codomain
-- inline) before the substitution that needs those names — so this
-- parser never needs lookahead.

export
parseNamedTypingRule : Rule TypingRule
parseNamedTypingRule =
  -- Context
  (str_ "ctx-emp" $> CtxWfEmpty) <|>
  (do str_ "ctx-ext"; space
      (ctx, _) <- parseNamedCtx
      case ctx of
        g :< ty => pure (CtxWfExt g ty)
        [<]     => fail "ctx-ext: requires non-empty context") <|>
  (do str_ "ctx-refl"; space; (ctx, _) <- parseNamedCtx; pure (CtxEqRefl ctx)) <|>
  (do str_ "ctx-sym"; space
      (ctx1, _) <- parseNamedCtx; sp; str_ "≐"; sp; (ctx0, _) <- parseNamedCtx
      pure (CtxEqSym ctx0 ctx1)) <|>
  (do str_ "ctx-trans"; space
      (ctx0, _) <- parseNamedCtx; sp; str_ "≐"; sp; (ctx2, _) <- parseNamedCtx
      sp; str_ "via"; sp; (ctx1, _) <- parseNamedCtx
      pure (CtxEqTrans ctx0 ctx1 ctx2)) <|>
  -- Substitution wf
  (do str_ "sub-term"; space
      (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; _ <- parseSub env
      pure (SubWfTerminal ctx)) <|>
  (do str_ "sub-ext"; space
      (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      sigma <- parseSub env; sp; str_ "to"; sp; (delta, _) <- parseNamedCtx
      case (sigma, delta) of
        (Ext s e, d :< ty) => pure (SubWfExt s e ctx d ty)
        _ => fail "sub-ext: expected σ, e and non-empty target context") <|>
  -- Substitution eq
  (do str_ "sub-refl"; space
      (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      s <- parseSub env; sp; char_ ':'; sp; (d, _) <- parseNamedCtx
      pure (SubEqRefl s ctx d)) <|>
  (do str_ "sub-sym"; space
      (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      s1 <- parseSub env; sp; str_ "≐"; sp; s0 <- parseSub env; sp; char_ ':'; sp; (d, _) <- parseNamedCtx
      pure (SubEqSym s0 s1 ctx d)) <|>
  (do str_ "sub-trans"; space
      (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      s0 <- parseSub env; sp; str_ "≐"; sp; s2 <- parseSub env; sp; char_ ':'; sp; (d, _) <- parseNamedCtx
      sp; str_ "via"; sp; s1 <- parseSub env
      pure (SubEqTrans s0 s1 s2 ctx d)) <|>
  -- Normal substitution wf (ext-eq before ext — longer keyword first)
  (do str_ "sub-norm-term"; space
      (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; _ <- parseSubNorm env
      pure (SubNormWfTerminal ctx)) <|>
  (do str_ "sub-norm-ext-eq"; space
      (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      full0 <- parseSubNorm env; sp; str_ "≐"; sp; full1 <- parseSubNorm env
      sp; char_ ':'; sp; (delta, _) <- parseNamedCtx
      case (full0, full1, delta) of
        (es0 :< t0, es1 :< t1, d :< ty) => pure (SubNormEqExt es0 es1 t0 t1 ctx d ty)
        _ => fail "sub-norm-ext-eq: expected e˲, t = e˲', t' and non-empty target context") <|>
  (do str_ "sub-norm-ext"; space
      (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      sigma <- parseSubNorm env; sp; str_ "to"; sp; (delta, _) <- parseNamedCtx
      case (sigma, delta) of
        (es :< e, d :< ty) => pure (SubNormWfExt es e ctx d ty)
        _ => fail "sub-norm-ext: expected e˲, e and non-empty target context") <|>
  -- Normal substitution eq
  (do str_ "sub-norm-refl"; space
      (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      s <- parseSubNorm env; sp; char_ ':'; sp; (d, _) <- parseNamedCtx
      pure (SubNormEqRefl s ctx d)) <|>
  (do str_ "sub-norm-sym"; space
      (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      s1 <- parseSubNorm env; sp; str_ "≐"; sp; s0 <- parseSubNorm env; sp; char_ ':'; sp; (d, _) <- parseNamedCtx
      pure (SubNormEqSym s0 s1 ctx d)) <|>
  (do str_ "sub-norm-trans"; space
      (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      s0 <- parseSubNorm env; sp; str_ "≐"; sp; s2 <- parseSubNorm env; sp; char_ ':'; sp; (d, _) <- parseNamedCtx
      sp; str_ "via"; sp; s1 <- parseSubNorm env
      pure (SubNormEqTrans s0 s1 s2 ctx d)) <|>
  -- Type wf
  (do str_ "ty-zero"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; ty <- parseTy env
      case ty of
        Ty.ZeroTy => pure (TyWfZero ctx)
        _         => fail "ty-zero: expected 𝟘") <|>
  (do str_ "ty-one";  space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; ty <- parseTy env
      case ty of
        Ty.OneTy => pure (TyWfOne ctx)
        _        => fail "ty-one: expected 𝟙") <|>
  (do str_ "ty-nat";  space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; ty <- parseTy env
      case ty of
        Ty.NatTy => pure (TyWfNat ctx)
        _        => fail "ty-nat: expected ℕ") <|>
  (do str_ "ty-univ"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; ty <- parseTy env
      case ty of
        Ty.UniverseTy => pure (TyWfUniverse ctx)
        _             => fail "ty-univ: expected 𝕌") <|>
  (do str_ "ty-pi"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; ty <- parseTy env
      case ty of
        PiTy a b => pure (TyWfPi ctx a b)
        _        => fail "ty-pi: expected (x:A) → B") <|>
  (do str_ "ty-sigma"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; ty <- parseTy env
      case ty of
        SigmaTy a b => pure (TyWfSigma ctx a b)
        _           => fail "ty-sigma: expected (x:A) ⨯ B") <|>
  (do str_ "ty-quotient"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; ty <- parseTy env
      case ty of
        Quotient a r => pure (TyWfQuotient ctx a r)
        _            => fail "ty-quotient: expected A / (x y. R)") <|>
  (do str_ "ty-wf-subst"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      sigma <- parseSub env; sp; str_ "to"; sp; (delta, denv) <- parseNamedCtx; sp; str_ "⊦"; sp
      a <- parseTy denv
      pure (TyWfSubst ctx delta sigma a)) <|>
  (do str_ "ty-eq-form"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; ty <- parseTy env
      case ty of
        Ty.EqTy l r a => pure (TyWfEq ctx l r a)
        _             => fail "ty-eq-form: expected l ≡ r ∈ A") <|>
  (do str_ "ty-el"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; ty <- parseTy env
      case ty of
        El e => pure (TyWfEl ctx e)
        _    => fail "ty-el: expected El e") <|>
  -- Type eq
  (do str_ "ty-refl"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; ty <- parseTy env
      pure (TyEqRefl ctx ty)) <|>
  (do str_ "ty-sym"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      ty1 <- parseTy env; sp; str_ "≐"; sp; ty0 <- parseTy env
      pure (TyEqSym ctx ty0 ty1)) <|>
  (do str_ "ty-trans"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      ty0 <- parseTy env; sp; str_ "≐"; sp; ty2 <- parseTy env; sp; str_ "via"; sp; ty1 <- parseTy env
      pure (TyEqTrans ctx ty0 ty1 ty2)) <|>
  (do str_ "ty-eq-cong"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      ty0 <- parseTy env; sp; str_ "≐"; sp; ty1 <- parseTy env
      case (ty0, ty1) of
        (Ty.EqTy a0 b0 t0, Ty.EqTy a1 b1 t1) => pure (TyEqCongEqTy ctx a0 b0 t0 a1 b1 t1)
        _ => fail "ty-eq-cong: expected (a₀ ≡ b₀ ∈ T₀) = (a₁ ≡ b₁ ∈ T₁)") <|>
  (do str_ "ty-el-cong"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      ty0 <- parseTy env; sp; str_ "≐"; sp; ty1 <- parseTy env
      case (ty0, ty1) of
        (Ty.El t0, Ty.El t1) => pure (TyEqCongEl ctx t0 t1)
        _ => fail "ty-el-cong: expected El t₀ = El t₁") <|>
  (do str_ "ty-eq-subst"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      sigma0 <- parseSub env; sp; str_ "≐"; sp; sigma1 <- parseSub env
      sp; str_ "to"; sp; (delta, denv) <- parseNamedCtx; sp; str_ "⊦"; sp
      a0 <- parseTy denv; sp; str_ "≐"; sp; a1 <- parseTy denv
      pure (TyEqSubst ctx delta sigma0 sigma1 a0 a1)) <|>
  -- Element wf: intro / elim  (longer keywords before shorter sharing same prefix)
  (do str_ "el-var"; space
      (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; x <- parseLocalIdentifier
      case resolveName env x of
        Just n  => pure (ElemWfVar ctx n)
        Nothing => fail "el-var: unbound identifier '\{x}'") <|>
  (do str_ "el-one"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; str_ "()"
      pure (ElemWfOneIntro ctx)) <|>
  (do str_ "el-zero"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; str_ "Z"
      pure (ElemWfZeroIntro ctx)) <|>
  (do str_ "el-suc"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      str_ "S"; space; e <- parseElemAtom env
      pure (ElemWfSucIntro ctx e)) <|>
  (do str_ "el-pi-i"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      str_ "λ"; sp; x <- parseLocalIdentifier; sp; char_ '.'; sp
      f <- parseElemPostfix (env :< x)
      sp; char_ ':'; sp; ty <- parseTy env
      case ty of
        PiTy a b => pure (ElemWfPiIntro ctx f a b)
        _        => fail "el-pi-i: expected (x:A) → B after :") <|>
  (do str_ "el-pi-e"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      char_ '('; sp; f <- parseElem env; sp; char_ ':'; sp; ty <- parseTy env; sp; char_ ')'
      sp; e <- parseElemAtom env
      case ty of
        PiTy a b => pure (ElemWfPiApp ctx f a b e)
        _        => fail "el-pi-e: expected (x:A) → B") <|>
  (do str_ "el-sigma-i"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      case e of
        SigmaIntro u v => do
          sp; char_ ':'; sp; ty <- parseTy env
          case ty of
            SigmaTy a b => pure (ElemWfSigmaIntro ctx u v a b)
            _           => fail "el-sigma-i: expected (x:A) ⨯ B after :"
        _ => fail "el-sigma-i: expected u, v") <|>
  (do str_ "el-sigma-e1"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      char_ '('; sp; e <- parseElem env; sp; char_ ':'; sp; ty <- parseTy env; sp; char_ ')'
      sp; str_ ".π₁"
      case ty of
        SigmaTy a b => pure (ElemWfSigmaElim1 ctx e a b)
        _           => fail "el-sigma-e1: expected (x:A) ⨯ B") <|>
  (do str_ "el-sigma-e2"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      char_ '('; sp; e <- parseElem env; sp; char_ ':'; sp; ty <- parseTy env; sp; char_ ')'
      sp; str_ ".π₂"
      case ty of
        SigmaTy a b => pure (ElemWfSigmaElim2 ctx e a b)
        _           => fail "el-sigma-e2: expected (x:A) ⨯ B") <|>
  (do str_ "el-zero-e"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      case e of
        ZeroElim t => do
          sp; char_ ':'; sp; ty <- parseTy env
          pure (ElemWfZeroElim ctx t ty)
        _ => fail "el-zero-e: expected 𝟘-elim e") <|>
  (do str_ "el-nat-e"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      case e of
        NatElim z s t => do
          space; str_ "motive"; space
          -- The motive is a Ty in Γ ᐅ ℕ — ONE extra binder (see
          -- ElemWfNatElim's step: `substTy a (Ext Id NatIntro0)` only ever
          -- substitutes a single slot). `ih` is consumed here purely for
          -- surface symmetry with the step case's own `(n ih. s)` binder
          -- pair — it is NOT a real binder for the motive and must not be
          -- added to the environment `ty` is parsed against, or every
          -- index inside `ty` ends up off by one.
          char_ '('; sp; n <- parseLocalIdentifier; space; ih <- parseLocalIdentifier
          sp; char_ '.'; sp; ty <- parseTy (env :< n); sp; char_ ')'
          pure (ElemWfNatElim ctx z s t ty)
        _ => fail "el-nat-e: expected ℕ-elim z (n ih. s) t") <|>
  (do str_ "el-class"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      case e of
        Class a => do
          sp; char_ ':'; sp; ty <- parseTy env
          case ty of
            Quotient tyA r => pure (ElemWfClass ctx a tyA r)
            _              => fail "el-class: expected A / (x y. R) after :"
        _ => fail "el-class: expected class a") <|>
  -- el-quot-elim-cong before el-quot-elim (longer keyword first)
  (do str_ "el-quot-elim-cong"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      str_ "quot-elim"; space
      char_ '('; sp; a0 <- parseLocalIdentifier; sp; char_ '.'; sp; f0 <- parseElem (env :< a0); sp; char_ ')'
      sp; str_ "≐"; sp
      char_ '('; sp; a1 <- parseLocalIdentifier; sp; char_ '.'; sp; f1 <- parseElem (env :< a1); sp; char_ ')'; space
      char_ '('; sp; q0 <- parseElem env; sp; str_ "≐"; sp; q1 <- parseElem env
      sp; char_ ':'; sp; ty <- parseTy env; sp; char_ ')'
      space; str_ "motive"; space
      char_ '('; sp; qn <- parseLocalIdentifier; sp; char_ '.'; sp
      motive <- parseTy (env :< qn); sp; char_ ')'
      case ty of
        Quotient tyA r => pure (ElemEqCongQuotElim ctx tyA r motive f0 f1 q0 q1)
        _              => fail "el-quot-elim-cong: expected quot-elim (a. f₀) ≐ (a. f₁) (q₀ ≐ q₁ : A / R) motive (q'. B)") <|>
  (do str_ "el-quot-elim"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      str_ "quot-elim"; space
      char_ '('; sp; a <- parseLocalIdentifier; sp; char_ '.'; sp; f <- parseElem (env :< a); sp; char_ ')'; space
      char_ '('; sp; q <- parseElem env; sp; char_ ':'; sp; ty <- parseTy env; sp; char_ ')'
      space; str_ "motive"; space
      char_ '('; sp; qn <- parseLocalIdentifier; sp; char_ '.'; sp
      motive <- parseTy (env :< qn); sp; char_ ')'
      case ty of
        Quotient tyA r => pure (ElemWfQuotElim ctx tyA r motive f q)
        _              => fail "el-quot-elim: expected quot-elim (a. f) (q : A / R) motive (q'. B)") <|>
  (do str_ "el-wf-subst"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      sigma <- parseSub env; sp; str_ "to"; sp; (delta, denv) <- parseNamedCtx; sp; str_ "⊦"; sp
      t <- parseElem denv; sp; char_ ':'; sp; a <- parseTy denv
      pure (ElemWfSubst ctx delta sigma t a)) <|>
  -- el-reflect before el-refl (shares "el-refl" prefix at token level)
  (do str_ "el-reflect"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      sp; char_ ':'; sp; char_ '('; sp; ty <- parseTy env; sp; char_ ')'
      sp; str_ "reflect"
      case ty of
        Ty.EqTy a0 a1 a => pure (ElemEqReflection ctx e a0 a1 a)
        _               => fail "el-reflect: expected equality type") <|>
  (do str_ "el-refl"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      str_ "Refl"; sp; char_ ':'; sp; e <- parseElemAtom env; sp; str_ "∈"; sp; ty <- parseTy env
      pure (ElemWfRefl ctx e ty)) <|>
  -- el-ty-coe-eq before el-ty-coe (longer keyword first)
  (do str_ "el-ty-coe-eq"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      e0 <- parseElem env; sp; str_ "≐"; sp; e1 <- parseElem env
      sp; char_ ':'; sp; ty0 <- parseTy env; sp; str_ "↝"; sp; ty1 <- parseTy env
      pure (ElemEqTyCoe ctx e0 e1 ty0 ty1)) <|>
  (do str_ "el-ty-coe"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      sp; char_ ':'; sp; ty0 <- parseTy env; sp; str_ "↝"; sp; ty1 <- parseTy env
      pure (ElemWfTyCoe ctx e ty0 ty1)) <|>
  (do str_ "el-ctx-coe"; space
      (ctx0, env0) <- parseNamedCtx; sp; str_ "≐"; sp; (ctx1, env1) <- parseNamedCtx
      sp; str_ "⊦"; sp; e <- parseElem env1; sp; char_ ':'; sp; ty <- parseTy env1
      pure (ElemWfCtxCoe ctx0 ctx1 e ty)) <|>
  -- Element wf: universe codes
  (do str_ "el-zero-ty"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      sp; char_ ':'; sp; str_ "𝕌"
      case e of
        Elem.ZeroTy => pure (ElemWfZeroTy ctx)
        _           => fail "el-zero-ty: expected 𝟘") <|>
  (do str_ "el-one-ty"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      sp; char_ ':'; sp; str_ "𝕌"
      case e of
        Elem.OneTy => pure (ElemWfOneTy ctx)
        _          => fail "el-one-ty: expected 𝟙") <|>
  (do str_ "el-nat-ty"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      sp; char_ ':'; sp; str_ "𝕌"
      case e of
        Elem.NatTy => pure (ElemWfNatTy ctx)
        _          => fail "el-nat-ty: expected ℕ") <|>
  (do str_ "el-pi-ty"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      sp; char_ ':'; sp; str_ "𝕌"
      case e of
        Elem.PiTy a b => pure (ElemWfPiTy ctx a b)
        _             => fail "el-pi-ty: expected (x:A) → B") <|>
  (do str_ "el-sigma-ty"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      sp; char_ ':'; sp; str_ "𝕌"
      case e of
        Elem.SigmaTy a b => pure (ElemWfSigmaTy ctx a b)
        _                => fail "el-sigma-ty: expected (x:A) ⨯ B") <|>
  (do str_ "el-eq-ty"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      sp; char_ ':'; sp; str_ "𝕌"
      case e of
        Elem.EqTy l r a => pure (ElemWfEqTy ctx l r a)
        _               => fail "el-eq-ty: expected l ≡ r ∈ A") <|>
  -- Signature (sig-var-eq before sig-var before sig — longer keywords first)
  (do str_ "sig-var-eq"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      case e of
        SigVar x sigma => pure (ElemEqSigVar ctx sigma x)
        _              => fail "sig-var-eq: expected x[σ]") <|>
  (do str_ "sig-var"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; e <- parseElem env
      case e of
        SigVar x sigma => pure (ElemWfSigVar ctx sigma x)
        _              => fail "sig-var: expected x[σ]") <|>
  (do str_ "sig"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      x <- Nova.Foundation.Parser.parseSigIdentifier; sp; str_ "≔"; sp
      a <- parseElem env; sp; char_ ':'; sp; ty <- parseTy env
      pure (SigExt ctx x a ty)) <|>
  -- Element equality (el-ty-coe-eq already above; el-eq-trans before el-eq-ty for safety)
  (do str_ "el-eq-refl"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      e <- parseElem env; sp; char_ ':'; sp; ty <- parseTy env
      pure (ElemEqRefl ctx e ty)) <|>
  (do str_ "el-eq-sym"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      e1 <- parseElem env; sp; str_ "≐"; sp; e0 <- parseElem env; sp; char_ ':'; sp; ty <- parseTy env
      pure (ElemEqSym ctx e0 e1 ty)) <|>
  (do str_ "el-eq-trans"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      e0 <- parseElem env; sp; str_ "≐"; sp; e2 <- parseElem env; sp; char_ ':'; sp; ty <- parseTy env
      sp; str_ "via"; sp; e1 <- parseElem env
      pure (ElemEqTrans ctx e0 e1 e2 ty)) <|>
  (do str_ "el-suc-cong"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      e0 <- parseElem env; sp; str_ "≐"; sp; e1 <- parseElem env
      case (e0, e1) of
        (NatIntro1 t0, NatIntro1 t1) => pure (ElemEqCongSuc ctx t0 t1)
        _ => fail "el-suc-cong: expected S t₀ = S t₁") <|>
  (do str_ "el-app-cong"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      char_ '('; sp; f0 <- parseElem env; sp; str_ "≐"; sp; f1 <- parseElem env
      sp; char_ ':'; sp; ty <- parseTy env; sp; char_ ')'
      sp; a0 <- parseElemAtom env; sp; str_ "≐"; sp; a1 <- parseElemAtom env
      case ty of
        PiTy a b => pure (ElemEqCongPiApp ctx f0 f1 a b a0 a1)
        _        => fail "el-app-cong: expected (x:A) → B") <|>
  -- el-class-cong before el-quot-eq (both share the "el-c"/"el-q" split, no
  -- real ambiguity, kept together for readability)
  (do str_ "el-class-cong"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      e0 <- parseElem env; sp; str_ "≐"; sp; e1 <- parseElem env
      sp; char_ ':'; sp; ty <- parseTy env
      case (e0, e1, ty) of
        (Class a0, Class a1, Quotient tyA r) => pure (ElemEqCongClass ctx tyA r a0 a1)
        _ => fail "el-class-cong: expected class a₀ = class a₁ : A / R") <|>
  (do str_ "el-quot-eq"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      e0 <- parseElem env; sp; str_ "≐"; sp; e1 <- parseElem env
      sp; char_ ':'; sp; ty <- parseTy env
      sp; str_ "via"; sp; witness <- parseElem env
      case (e0, e1, ty) of
        (Class a, Class b, Quotient tyA r) => pure (ElemEqQuotient ctx tyA r a b witness)
        _ => fail "el-quot-eq: expected class a = class b : A / R via r") <|>
  (do str_ "el-eq-subst"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      sigma0 <- parseSub env; sp; str_ "≐"; sp; sigma1 <- parseSub env
      sp; str_ "to"; sp; (delta, denv) <- parseNamedCtx; sp; str_ "⊦"; sp
      t0 <- parseElem denv; sp; str_ "≐"; sp; t1 <- parseElem denv; sp; char_ ':'; sp; a <- parseTy denv
      pure (ElemEqSubst ctx delta sigma0 sigma1 t0 t1 a)) <|>
  -- Telescope equality
  (do str_ "tel-refl"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; tel <- parseTel env
      pure (TelEqRefl ctx tel)) <|>
  (do str_ "tel-sym"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      tel1 <- parseTel env; sp; str_ "≐"; sp; tel0 <- parseTel env
      pure (TelEqSym ctx tel0 tel1)) <|>
  (do str_ "tel-trans"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      tel0 <- parseTel env; sp; str_ "≐"; sp; tel2 <- parseTel env; sp; str_ "via"; sp; tel1 <- parseTel env
      pure (TelEqTrans ctx tel0 tel1 tel2)) <|>
  -- Spine equality
  (do str_ "sp-refl"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      spine <- parseSpine env; sp; char_ ':'; sp; tel <- parseTel env
      pure (SpineEqRefl ctx spine tel)) <|>
  (do str_ "sp-sym"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      s1 <- parseSpine env; sp; str_ "≐"; sp; s0 <- parseSpine env; sp; char_ ':'; sp; tel <- parseTel env
      pure (SpineEqSym ctx s0 s1 tel)) <|>
  (do str_ "sp-trans"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      s0 <- parseSpine env; sp; str_ "≐"; sp; s2 <- parseSpine env; sp; char_ ':'; sp; tel <- parseTel env
      sp; str_ "via"; sp; s1 <- parseSpine env
      pure (SpineEqTrans ctx s0 s1 s2 tel))

-- Parse a list of typing rules, each prefixed by "- ".
export
parseNamedListTypingRule : Rule (List TypingRule)
parseNamedListTypingRule = many (do sp; char_ '-'; space; parseNamedTypingRule)

-- ===== JudgementForm parser =====
--
-- Keyword-first: each form starts with a unique keyword. Every Γ/Δ is
-- self-contained (see parseNamedCtx) — a .target file has no ctx-ext trail of
-- its own, so this is exactly the case where the named forms (Γ ᐅ x:T,
-- (x:A) → B, λx. f, ℕ-elim z (n ih. s) t, ...) matter most: there is
-- nothing else to fall back on.
--
--   ctx-wf  Γ                   (JfCtxWf)
--   ctx-eq  Γ = Γ'              (JfCtxEq)
--   sub-wf  σ : Γ ⇒ Δ          (JfSubWf)
--   sub-eq  σ = σ' : Γ ⇒ Δ    (JfSubEq)
--   sub-norm-wf  e˲ : Γ ⇒ Δ norm       (JfSubNormWf)
--   sub-norm-eq  e˲ = e˲' : Γ ⇒ Δ norm (JfSubNormEq)
--   ty-wf   Γ ⊦ T               (JfTyWf)
--   ty-eq   Γ ⊦ T = T'          (JfTyEq)
--   el-wf   Γ ⊦ t : T           (JfElemWf)
--   el-eq   Γ ⊦ t = t' : T      (JfElemEq)
--   tel-wf  Γ ⊦ Δ               (JfTelWf)
--   tel-eq  Γ ⊦ Δ = Δ'          (JfTelEq)
--   sp-wf   Γ ⊦ ē : Δ           (JfSpineWf)
--   sp-eq   Γ ⊦ ē = ē' : Δ     (JfSpineEq)

export
parseNamedJudgementForm : Rule JudgementForm
parseNamedJudgementForm =
  (do str_ "ctx-wf"; space; (ctx, env) <- parseNamedCtx
      pure (JfCtxWf ctx)) <|>
  (do str_ "ctx-eq"; space
      (ctx, env) <- parseNamedCtx; sp; str_ "≐"; sp; (ctx', env') <- parseNamedCtx
      pure (JfCtxEq (ctx, ctx'))) <|>
  (do str_ "sub-wf"; space
      s <- parseSub [<]; sp; char_ ':'; sp; (g, genv) <- parseNamedCtx; sp; str_ "⇒"; sp; (d, _) <- parseNamedCtx
      pure (JfSubWf (s, g, d))) <|>
  (do str_ "sub-eq"; space
      s <- parseSub [<]; sp; str_ "≐"; sp; s' <- parseSub [<]; sp
      char_ ':'; sp; (g, genv) <- parseNamedCtx; sp; str_ "⇒"; sp; (d, _) <- parseNamedCtx
      pure (JfSubEq (s, s', g, d))) <|>
  (do str_ "sub-norm-wf"; space
      s <- parseSubNorm [<]; sp; char_ ':'; sp; (g, genv) <- parseNamedCtx; sp; str_ "⇒"; sp; (d, _) <- parseNamedCtx
      sp; str_ "norm"
      pure (JfSubNormWf (s, g, d))) <|>
  (do str_ "sub-norm-eq"; space
      s <- parseSubNorm [<]; sp; str_ "≐"; sp; s' <- parseSubNorm [<]; sp
      char_ ':'; sp; (g, genv) <- parseNamedCtx; sp; str_ "⇒"; sp; (d, _) <- parseNamedCtx
      sp; str_ "norm"
      pure (JfSubNormEq (s, s', g, d))) <|>
  (do str_ "ty-wf"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; ty <- parseTy env
      pure (JfTyWf (ctx, ty))) <|>
  (do str_ "ty-eq"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      ty <- parseTy env; sp; str_ "≐"; sp; ty' <- parseTy env
      pure (JfTyEq (ctx, ty, ty'))) <|>
  (do str_ "el-wf"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      e <- parseElem env; sp; char_ ':'; sp; ty <- parseTy env
      pure (JfElemWf (ctx, e, ty))) <|>
  (do str_ "el-eq"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      e <- parseElem env; sp; str_ "≐"; sp; e' <- parseElem env; sp; char_ ':'; sp; ty <- parseTy env
      pure (JfElemEq (ctx, e, e', ty))) <|>
  (do str_ "tel-wf"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp; tel <- parseTel env
      pure (JfTelWf (ctx, tel))) <|>
  (do str_ "tel-eq"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      tel <- parseTel env; sp; str_ "≐"; sp; tel' <- parseTel env
      pure (JfTelEq (ctx, tel, tel'))) <|>
  (do str_ "sp-wf"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      spine <- parseSpine env; sp; char_ ':'; sp; tel <- parseTel env
      pure (JfSpineWf (ctx, spine, tel))) <|>
  (do str_ "sp-eq"; space; (ctx, env) <- parseNamedCtx; sp; str_ "⊦"; sp
      spine <- parseSpine env; sp; str_ "≐"; sp; spine' <- parseSpine env; sp
      char_ ':'; sp; tel <- parseTel env
      pure (JfSpineEq (ctx, spine, spine', tel)))

-- Parse a list of judgement forms, each prefixed by "- ".
export
parseNamedListJudgementForm : Rule (List JudgementForm)
parseNamedListJudgementForm = many (do sp; char_ '-'; space; parseNamedJudgementForm)
