module Nova.Foundation.Named

-- Named term syntax: the NameEnv discipline, local identifiers, and the
-- named pretty-printer for core terms (see docs/NovaElaboration.txt for
-- the surface syntax that builds on this).
--
-- There is no separate "named" AST: a NameEnv is a list of names
-- parallel to the Ctx being built (rightmost = innermost = de Bruijn
-- index 0); parsing resolves a name to an index by position, and
-- printing invents deterministic, type-biased names for binders (the
-- core carries none).

import Data.SnocList
import Data.Maybe

import Me.Russoul.Text.Lexer.Token
import Me.Russoul.Text.Lexer
import Me.Russoul.Text.Parser
import Me.Russoul.Text.Parser.OverToken
import Me.Russoul.Text.Position
import Me.Russoul.Text.Range

import Nova.Foundation.Syntax
import Nova.Foundation.Parser

%default covering

-- Optional whitespace between tokens (Nova.Foundation.Parser.sp is private
-- to that module, so this is its own local copy).
sp : Rule ()
sp = optSpace

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
  usesIndexTy k (Ty.SigVar x es) = usesIndexSubNorm k es

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
  usesIndexElem k (QuotTy a r) = usesIndexElem k a || usesIndexElem (S (S k)) r
  usesIndexElem k Refl = False
  usesIndexElem k (SigVar x es) = usesIndexSubNorm k es
  usesIndexElem k (Class a) = usesIndexElem k a
  usesIndexElem k (QuotElim f q) = usesIndexElem k f || usesIndexElem k q

  usesIndexSubNorm : Nat -> SubNorm -> Bool
  usesIndexSubNorm k [<] = False
  usesIndexSubNorm k (es :< e) = usesIndexSubNorm k es || usesIndexElem k e

-- ===== Sub and Elem (mutually recursive) =====

mutual
  ||| The empty substitution prints as nothing at all (not "·" — see
  ||| NovaNamedSyntax.txt); a non-empty one is a bare comma-separated
  ||| element list, e.g. "n, A, m" for what used to be "·, n, A, m".
  export
  prettySubN : NameEnv -> Sub -> String
  prettySubN env s = fromMaybe "" (prettySubElemsN env s)

  -- Nothing = no elements printed yet (the empty/Terminal case); Just str
  -- = the rendered comma-separated element list so far. Id/Wk/Chain can
  -- never be constructed by any rule in this grammar anymore (see
  -- NamedParser.idr's header) — reaching one here means a real bug
  -- upstream (e.g. something bypassed the named parser/checker), so this
  -- crashes loudly rather than silently printing an unreparseable string.
  prettySubElemsN : NameEnv -> Sub -> Maybe String
  prettySubElemsN env (Ext s e) =
    case prettySubElemsN env s of
      Nothing   => Just (prettyElemNoCommaN env e)
      Just rest => Just (rest ++ ", " ++ prettyElemNoCommaN env e)
  prettySubElemsN env Terminal = Nothing
  prettySubElemsN env Id = assert_total (idris_crash "prettySubN: unreachable Id (no rule constructs it)")
  prettySubElemsN env Wk = assert_total (idris_crash "prettySubN: unreachable Wk (no rule constructs it)")
  prettySubElemsN env (Chain _ _) = assert_total (idris_crash "prettySubN: unreachable Chain (no rule constructs it)")

  export
  prettyElemN : NameEnv -> Elem -> String
  prettyElemN env (SigmaIntro e e') = prettyElemNoCommaN env e ++ ", " ++ prettyElemN env e'
  prettyElemN env e = prettyElemNoCommaN env e

  export
  prettyElemNoCommaN : NameEnv -> Elem -> String
  prettyElemNoCommaN env (Elem.PiTy e e') =
    if usesIndexElem 0 e'
      -- Domain sits inside an explicit "(x: ... )" binder, already fully
      -- delimited by the closing paren, so it can be printed unrestricted
      -- (parseElem, not parseElemPrefix, is what actually parses it back)
      -- instead of forcing another, redundant, pair of parens around it.
      then let x = freshGeneric env
           in "(" ++ x ++ ":" ++ prettyElemN env e ++ ") → " ++ prettyElemNoCommaN (env :< x) e'
      else prettyElemPrefixN env e ++ " → " ++ prettyElemNoCommaN (env :< wildcard) e'
  prettyElemNoCommaN env (Elem.SigmaTy e e') =
    if usesIndexElem 0 e'
      then let x = freshGeneric env
           in "(" ++ x ++ ":" ++ prettyElemN env e ++ ") ⨯ " ++ prettyElemNoCommaN (env :< x) e'
      else prettyElemPrefixN env e ++ " ⨯ " ++ prettyElemNoCommaN (env :< wildcard) e'
  prettyElemNoCommaN env (Elem.EqTy e0 e1 e2) =
    prettyElemPrefixN env e0 ++ " ≡ " ++ prettyElemPrefixN env e1 ++ " ∈ " ++ prettyElemPrefixN env e2
  prettyElemNoCommaN env (QuotTy e r) =
    let x = freshForTy (El e) env
        y = freshGeneric (env :< x)
    in prettyElemPrefixN env e ++ " / (" ++ x ++ " " ++ y ++ ". " ++ prettyElemNoCommaN (env :< x :< y) r ++ ")"
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
  prettyElemPrefixN env (QuotElim f q) =
    let a = if usesIndexElem 0 f then freshGeneric env else wildcard
    in "quot-elim (" ++ a ++ ". " ++ prettyElemN (env :< a) f ++ ") " ++ prettyElemAtomN env q
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

  ||| t˲ ::= ε | t˲ , t — the empty normal substitution prints as nothing
  ||| at all, same as Sub above (e.g. `vect[]`, not `vect[·]`).
  export
  prettySubNormN : NameEnv -> SubNorm -> String
  prettySubNormN env s = fromMaybe "" (prettySubNormElemsN env s)

  prettySubNormElemsN : NameEnv -> SubNorm -> Maybe String
  prettySubNormElemsN env [<] = Nothing
  prettySubNormElemsN env (es :< e) =
    case prettySubNormElemsN env es of
      Nothing   => Just (prettyElemNoCommaN env e)
      Just rest => Just (rest ++ ", " ++ prettyElemNoCommaN env e)

-- ===== Ty =====

mutual
  export
  prettyTyN : NameEnv -> Ty -> String
  prettyTyN env (Ty.EqTy e0 e1 a) =
    prettyElemPrefixN env e0 ++ " ≡ " ++ prettyElemPrefixN env e1 ++ " ∈ " ++ prettyTyArrowN env a
  prettyTyN env ty = prettyTyArrowN env ty

  prettyTyArrowN : NameEnv -> Ty -> String
  prettyTyArrowN env (Ty.PiTy a b) =
    if usesIndexTy 0 b
      -- Domain sits inside an explicit "(x: ... )" binder, already fully
      -- delimited by the closing paren, so it can be printed unrestricted
      -- (parseTy, not parseTyEl, is what actually parses it back) instead
      -- of forcing another, redundant, pair of parens around it.
      then let x = freshForTy a env
           in "(" ++ x ++ ":" ++ prettyTyN env a ++ ") → " ++ prettyTyArrowN (env :< x) b
      else prettyTyElN env a ++ " → " ++ prettyTyArrowN (env :< wildcard) b
  prettyTyArrowN env (Ty.SigmaTy a b) =
    if usesIndexTy 0 b
      then let x = freshForTy a env
           in "(" ++ x ++ ":" ++ prettyTyN env a ++ ") ⨯ " ++ prettyTyArrowN (env :< x) b
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
  prettyTyAtomN env (Ty.SigVar x es) = x ++ "[" ++ prettySubNormN env es ++ "]"
  prettyTyAtomN env ty = "(" ++ prettyTyN env ty ++ ")"

-- ===== Ctx =====

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

