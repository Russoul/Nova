module Nova.Elaboration.Named

-- Named term syntax: the NameEnv discipline, local identifiers, and the
-- named pretty-printer for core terms (see docs/NovaElaboration.txt for
-- the surface syntax that builds on this).
--
-- There is no separate "named" AST: a NameEnv is a list of names
-- parallel to the Ctx being built (rightmost = innermost = de Bruijn
-- index 0); parsing resolves a name to an index by position, and
-- printing invents deterministic, type-biased names for binders (the
-- core carries none).

import Data.List
import Data.List1
import Data.SnocList
import Data.Maybe

import Me.Russoul.Text.Lexer.Token
import Me.Russoul.Text.Lexer
import Me.Russoul.Text.Parser
import Me.Russoul.Text.Parser.OverToken
import Me.Russoul.Text.Position
import Me.Russoul.Text.Range

import Nova.Kernel.Syntax
import Nova.Kernel.Parser

import Nova.Elaboration.Surface

%default covering

-- Optional whitespace between tokens (Nova.Kernel.Parser.sp is private
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
-- Distinct from Nova.Kernel.Parser.parseSigIdentifier (which lexes
-- *signature* identifiers, always followed by `[...]` and therefore never
-- ambiguous with a local name). Local identifiers additionally allow `'`
-- in the continuation (but not as the first character), matching common
-- mathematical convention (`n'`, `ih'`, ...).
--
-- Known limitation (inherited from the rest of this parser, not
-- introduced here): a local variable literally spelled the same as a
-- reserved keyword token that can match with nothing required afterward
-- (`Z`, `⋆`, and prefix-of-keyword names like `Sn`, `classify`,
-- `Elem` immediately followed by more identifier characters with no
-- separating whitespace) can be misparsed, exactly as an equally-named
-- signature identifier already could be in the unnamed parser. Avoid
-- naming a local variable exactly `Z`/`S`/`El`/`class` or a prefix
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

candidatesProp : List String
candidatesProp = ["p", "q", "r"]

candidatesPrf : List String
candidatesPrf = ["h", "hp", "hq"]

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
-- El retired: a neutral code in type position gets the El-slot names
freshForTy (SigVar _ _) = freshFromList candidatesEl
freshForTy (CtxVar _) = freshFromList candidatesEl
freshForTy (PiApp _ _) = freshFromList candidatesEl
freshForTy PropTy = freshFromList candidatesProp
-- Prf retired: a prop in type position gets the proof-flavored names
freshForTy (Elem.EqTy _ _ _) = freshFromList candidatesPrf
freshForTy (Squash _) = freshFromList candidatesPrf
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
-- decide whether a Pi/Sigma binder can use the `A → B`/`A × B` sugar
-- (dropping the name entirely) instead of `(x:A) → B`/`(x:A) × B`: if the
-- codomain never references the domain's bound variable, there's nothing
-- to name. Mirrors the printer's own binder-depth bookkeeping exactly —
-- each nested binder increments `k` by however many slots it introduces.

||| A qualified name's final segment (prop.⊃ → ⊃) — how the source
||| spelled an opened operator.
lastSeg : String -> String
lastSeg x = pack (reverse (takeWhile (/= '.') (reverse (unpack x))))

||| How a Σ name SPELLS at an occurrence. A HOLE prints as the label
||| its operator wrote (`?a`, `?a/squashee`) rather than the
||| run-unique name it was minted under (`?mod.item.a/…`): the
||| qualification is machine-made, never written, and only noise in a
||| goal. Everything else prints as it is, parenthesised when it is
||| operator-shaped.
export
sigRefN : SigIdentifier -> String
sigRefN x =
  if isHoleName x then holeLabel x
  else if isOpName x then "(" ++ x ++ ")" else x

||| Is this spine the identity substitution over a context of length
||| n — ☐ₙ₋₁, ..., ☐₀? (How a Σ entry minted at the ambient context
||| is referenced at its own site.)
isIdSpineN : Nat -> SubNorm -> Bool
isIdSpineN n es = toList es == map CtxVar (reverse [0 .. minus n 1]) && n /= 0


mutual
  export
  usesIndexTy : Nat -> Ty -> Bool
  usesIndexTy = usesIndexElem

  usesIndexQSig : Nat -> QSig -> Bool
  usesIndexQSig k = any (usesIndexQTy k)

  usesIndexQTy : Nat -> QTy -> Bool
  usesIndexQTy k QU = False
  usesIndexQTy k (QEl t) = usesIndexQTm k t
  usesIndexQTy k (QPiExt a b) = usesIndexTy k a || usesIndexQTy (S k) b
  usesIndexQTy k (QPiInd u b) = usesIndexQTm k u || usesIndexQTy k b

  usesIndexQTm : Nat -> QTm -> Bool
  usesIndexQTm k (QVar _) = False
  usesIndexQTm k (QAppE f e) = usesIndexQTm k f || usesIndexElem k e
  usesIndexQTm k (QAppI f a) = usesIndexQTm k f || usesIndexQTm k a
  usesIndexQTm k (QEqC l r u) = usesIndexQTm k l || usesIndexQTm k r || usesIndexQTm k u

  usesIndexPoly : Nat -> Poly -> Bool
  usesIndexPoly k PHole = False
  usesIndexPoly k (PConst a) = usesIndexElem k a
  usesIndexPoly k (PProd f g) = usesIndexPoly k f || usesIndexPoly k g
  usesIndexPoly k (PSum f g) = usesIndexPoly k f || usesIndexPoly k g
  usesIndexPoly k (PSigma a f) = usesIndexElem k a || usesIndexPoly (S k) f
  usesIndexPoly k (PPi a f) = usesIndexElem k a || usesIndexPoly (S k) f

  export
  usesIndexElem : Nat -> Elem -> Bool
  usesIndexElem k (CtxVar n) = n == k
  usesIndexElem k (ZeroElim e) = usesIndexElem k e
  usesIndexElem k OneIntro = False
  usesIndexElem k NatIntro0 = False
  usesIndexElem k (NatIntro1 e) = usesIndexElem k e
  usesIndexElem k (NatElim z s t) = usesIndexElem k z || usesIndexElem (S (S k)) s || usesIndexElem k t
  usesIndexElem k (PiIntro e) = usesIndexElem (S k) e
  usesIndexElem k (PiApp f e) = usesIndexElem k f || usesIndexElem k e
  usesIndexElem k (Let a b) = usesIndexElem k a || usesIndexElem (S (S k)) b
  usesIndexElem k (SigmaIntro e e') = usesIndexElem k e || usesIndexElem k e'
  usesIndexElem k (SigmaElim1 e) = usesIndexElem k e
  usesIndexElem k (SigmaElim2 e) = usesIndexElem k e
  usesIndexElem k (Inj1 e) = usesIndexElem k e
  usesIndexElem k (Inj2 e) = usesIndexElem k e
  usesIndexElem k (SumElim l r t) = usesIndexElem (S k) l || usesIndexElem (S k) r || usesIndexElem k t
  usesIndexElem k Elem.ZeroTy = False
  usesIndexElem k Elem.OneTy = False
  usesIndexElem k Elem.NatTy = False
  usesIndexElem k UniverseTy = False
  usesIndexElem k PropTy = False
  usesIndexElem k TopTy = False
  usesIndexElem k (Elem.PiTy e e') = usesIndexElem k e || usesIndexElem (S k) e'
  usesIndexElem k (Elem.SigmaTy e e') = usesIndexElem k e || usesIndexElem (S k) e'
  usesIndexElem k (Elem.SumTy e e') = usesIndexElem k e || usesIndexElem k e'
  usesIndexElem k (Elem.EqTy e0 e1 t2) = usesIndexElem k e0 || usesIndexElem k e1 || usesIndexTy k t2
  usesIndexElem k (QuotTy a r) = usesIndexElem k a || usesIndexElem (S (S k)) r
  usesIndexElem k (SigVar x es) = usesIndexSubNorm k es
  usesIndexElem k (Class a) = usesIndexElem k a
  usesIndexElem k (QuotElim f q) = usesIndexElem k f || usesIndexElem k q
  usesIndexElem k (Squash t) = usesIndexTy k t
  usesIndexElem k Star = False
  usesIndexElem k (QSort sg j es) = usesIndexQSig k sg || usesIndexSubNorm k es
  usesIndexElem k (QCtor sg j es) = usesIndexQSig k sg || usesIndexSubNorm k es
  usesIndexElem k (QElim sg j ms fs es w) =
    usesIndexQSig k sg || any (usesIndexMotive) (zip (qPositions QKSort sg) ms)
      || any (usesIndexElem k) fs || usesIndexSubNorm k es || usesIndexElem k w
   where
    usesIndexMotive : (Nat, Ty) -> Bool
    usesIndexMotive (sj, m) = usesIndexTy (k + S (qArityLen sg sj)) m
  usesIndexElem k (Elem.NuTy f) = usesIndexPoly k f
  usesIndexElem k (Out t) = usesIndexElem k t
  usesIndexElem k (Corec p a f x) =
    usesIndexPoly k p || usesIndexElem k a || usesIndexElem (S k) f || usesIndexElem k x

  usesIndexSubNorm : Nat -> SubNorm -> Bool
  usesIndexSubNorm k [<] = False
  usesIndexSubNorm k (es :< e) = usesIndexSubNorm k es || usesIndexElem k e

-- ===== Sub and Elem (mutually recursive) =====

mutual
  ||| The empty substitution prints as nothing at all (not "·" — see
  ||| NovaNamedSyntax.txt); a non-empty one is a bare comma-separated
  ||| element list, e.g. "n, A, m" for what used to be "·, n, A, m".
  export
  prettySubN : FixTable -> NameEnv -> Sub -> String
  prettySubN tbl env s = fromMaybe "" (prettySubElemsN tbl env s)

  -- Nothing = no elements printed yet (the empty/Terminal case); Just str
  -- = the rendered comma-separated element list so far. Id/Wk/Chain can
  -- never be constructed by any rule in this grammar anymore (see
  -- NamedParser.idr's header) — reaching one here means a real bug
  -- upstream (e.g. something bypassed the named parser/checker), so this
  -- crashes loudly rather than silently printing an unreparseable string.
  prettySubElemsN : FixTable -> NameEnv -> Sub -> Maybe String
  prettySubElemsN tbl env (Ext s e) =
    case prettySubElemsN tbl env s of
      Nothing   => Just (prettyElemNoCommaN tbl env e)
      Just rest => Just (rest ++ ", " ++ prettyElemNoCommaN tbl env e)
  prettySubElemsN tbl env Terminal = Nothing
  prettySubElemsN tbl env Id = assert_total (idris_crash "prettySubN: unreachable Id (no rule constructs it)")
  prettySubElemsN tbl env Wk = assert_total (idris_crash "prettySubN: unreachable Wk (no rule constructs it)")
  prettySubElemsN tbl env (Chain _ _) = assert_total (idris_crash "prettySubN: unreachable Chain (no rule constructs it)")

  export
  prettyElemN : FixTable -> NameEnv -> Elem -> String
  prettyElemN tbl env (SigmaIntro e e') = prettyElemNoCommaN tbl env e ++ ", " ++ prettyElemN tbl env e'
  prettyElemN tbl env e = prettyElemNoCommaN tbl env e

  export
  prettyElemNoCommaN : FixTable -> NameEnv -> Elem -> String
  prettyElemNoCommaN tbl env (Elem.PiTy e e') =
    if usesIndexElem 0 e'
      -- Domain sits inside an explicit "(x: ... )" binder, already fully
      -- delimited by the closing paren, so it can be printed unrestricted
      -- (parseElem, not parseElemPrefix, is what actually parses it back)
      -- instead of forcing another, redundant, pair of parens around it.
      then let x = freshGeneric env
           in "(" ++ x ++ ":" ++ prettyElemN tbl env e ++ ") → " ++ prettyElemNoCommaN tbl (env :< x) e'
      else prettyElemOpN tbl env 0 e ++ " → " ++ prettyElemNoCommaN tbl (env :< wildcard) e'
  prettyElemNoCommaN tbl env (Elem.SigmaTy e e') =
    if usesIndexElem 0 e'
      then let x = freshGeneric env
           in "(" ++ x ++ ":" ++ prettyElemN tbl env e ++ ") × " ++ prettyElemNoCommaN tbl (env :< x) e'
      else prettyElemOpN tbl env 0 e ++ " × " ++ prettyElemNoCommaN tbl (env :< wildcard) e'
  prettyElemNoCommaN tbl env e@(Elem.SumTy _ _) = prettyElemSumN tbl env e
  prettyElemNoCommaN tbl env (Elem.EqTy e0 e1 t2) =
    prettyElemOpN tbl env 0 e0 ++ " ≡ " ++ prettyElemOpN tbl env 0 e1 ++ " ∈ " ++ prettyTyArrowN tbl env t2
  prettyElemNoCommaN tbl env (QuotTy e r) =
    let x = freshForTy e env
        y = freshGeneric (env :< x)
    in prettyElemOpN tbl env 0 e ++ " / (" ++ x ++ " " ++ y ++ ". " ++ prettyElemNoCommaN tbl (env :< x :< y) r ++ ")"
  prettyElemNoCommaN tbl env e = prettyElemOpN tbl env 0 e

  -- the ⊎ code binds tighter than the other infix element formers
  -- (chain at its own level; any non-sum component prints at the
  -- operator level, which parenthesizes arrows and pairs)
  prettyElemSumN : FixTable -> NameEnv -> Elem -> String
  prettyElemSumN tbl env (Elem.SumTy e e') =
    prettyElemOpN tbl env 0 e ++ " ⊎ " ++ prettyElemSumN tbl env e'
  prettyElemSumN tbl env e = prettyElemOpN tbl env 0 e

  -- t{1½}: operator applications, precedence-aware — parenthesized
  -- exactly when the operator binds looser than the context demands.
  -- An operator with no fixity in scope falls through to the prefix
  -- spelling ((+) a b), which is always valid.
  prettyElemOpN : FixTable -> NameEnv -> (minPrec : Nat) -> Elem -> String
  prettyElemOpN tbl env minP e@(PiApp (PiApp (SigVar op [<]) a) b) =
    -- fixity keys the OPENED bare token, Σ-names are qualified: a
    -- reference like prop.⊃ finds its fixity (and lays out) by its
    -- last segment — the spelling the source used
    case (isOpName op, lookup op tbl <|> lookup (lastSeg op) tbl) of
      (True, Just (assoc, p)) =>
        let lP = case assoc of AssocL => p; AssocR => S p
            rP = case assoc of AssocL => S p; AssocR => p
            body = prettyElemOpN tbl env lP a ++ " " ++ lastSeg op ++ " " ++ prettyElemOpN tbl env rP b
        in if p < minP then "(" ++ body ++ ")" else body
      _ => prettyElemPrefixN tbl env e
  prettyElemOpN tbl env minP e = prettyElemPrefixN tbl env e

  prettyElemPrefixN : FixTable -> NameEnv -> Elem -> String
  prettyElemPrefixN tbl env (PiIntro e) =
    let x = freshGeneric env
    in "λ" ++ x ++ ". " ++ prettyElemOpN tbl (env :< x) 0 e
  prettyElemPrefixN tbl env (Let a b) =
    -- surface-faithful: the unfolding-equation binder has no surface
    -- spelling and elaborator-produced bodies never reference it; it
    -- still enters the env (under a fresh Prf-flavored name) so a
    -- reference in hand-built core would at least print visibly
    let x = freshGeneric env
        h = freshFromList candidatesPrf (env :< x)
    in "let " ++ x ++ " ≔ " ++ prettyElemN tbl env a ++ " in "
         ++ prettyElemOpN tbl (env :< x :< h) 0 b
  prettyElemPrefixN tbl env (ZeroElim e) = "𝟘-elim " ++ prettyElemAtomN tbl env e
  prettyElemPrefixN tbl env (NatIntro1 e) = "S " ++ prettyElemAtomN tbl env e
  prettyElemPrefixN tbl env (NatElim z s t) =
    let n  = freshFromList candidatesNat env
        ih = freshIH (env :< n)
    in "ℕ-elim " ++ prettyElemAtomN tbl env z ++
       " (" ++ n ++ " " ++ ih ++ ". " ++ prettyElemAtomN tbl (env :< n :< ih) s ++ ") " ++
       prettyElemAtomN tbl env t
  prettyElemPrefixN tbl env (Inj1 a) = "inj₁ " ++ prettyElemAtomN tbl env a
  prettyElemPrefixN tbl env (Inj2 a) = "inj₂ " ++ prettyElemAtomN tbl env a
  prettyElemPrefixN tbl env (SumElim l r t) =
    let a = if usesIndexElem 0 l then freshGeneric env else wildcard
        b = if usesIndexElem 0 r then freshGeneric env else wildcard
    in "⊎-elim (" ++ a ++ ". " ++ prettyElemN tbl (env :< a) l ++ ") ("
         ++ b ++ ". " ++ prettyElemN tbl (env :< b) r ++ ") "
         ++ prettyElemAtomN tbl env t
  prettyElemPrefixN tbl env (Class a) = "class " ++ prettyElemAtomN tbl env a
  prettyElemPrefixN tbl env (Elem.NuTy f) = "ν " ++ prettyPolyAtomN tbl env f
  prettyElemPrefixN tbl env (Out t) = "out " ++ prettyElemAtomN tbl env t
  prettyElemPrefixN tbl env (Corec p a f x) =
    -- surface-faithful: the carried 𝔽 is not printed (it is the
    -- expected ν-type's, recovered at checking)
    let v = if usesIndexElem 0 f then freshGeneric env else wildcard
    in "corec (" ++ v ++ " : " ++ prettyElemNoCommaN tbl env a ++ ". "
         ++ prettyElemN tbl (env :< v) f ++ ") " ++ prettyElemAtomN tbl env x
  prettyElemPrefixN tbl env (QuotElim f q) =
    let a = if usesIndexElem 0 f then freshGeneric env else wildcard
    in "quot-elim (" ++ a ++ ". " ++ prettyElemN tbl (env :< a) f ++ ") " ++ prettyElemAtomN tbl env q
  prettyElemPrefixN tbl env e = prettyElemPostfixN tbl env e

  prettyElemPostfixN : FixTable -> NameEnv -> Elem -> String
  prettyElemPostfixN tbl env (SigmaElim1 e) = prettyElemPostfixN tbl env e ++ " .π₁"
  prettyElemPostfixN tbl env (SigmaElim2 e) = prettyElemPostfixN tbl env e ++ " .π₂"
  prettyElemPostfixN tbl env (PiApp f e) = prettyElemPostfixN tbl env f ++ " " ++ prettyElemAtomN tbl env e
  prettyElemPostfixN tbl env e = prettyElemAtomN tbl env e

  export
  ||| A QIIT sort, signature spelled out: `𝒮{U; (El ℕ) ⇛ ⬡0; …}.k[ē]`
  ||| — the signature is the sort's IDENTITY (structural, nameless),
  ||| so a diagnostic naming only `𝒮.k` hides exactly the part two
  ||| mismatched sorts differ in (an instantiated parameter, say).
  prettyQSortN : FixTable -> NameEnv -> QSig -> Nat -> SubNorm -> String
  prettyQSortN tbl env sg k es =
    "𝒮{" ++ concat (intersperse "; " (map (prettyQTyN tbl env) sg)) ++ "}." ++ show k ++
    "[" ++ prettySubNormN tbl env es ++ "]"

  prettyQTmN : FixTable -> NameEnv -> QTm -> String
  prettyQTmN tbl env (QVar i) = "⬡" ++ show i
  prettyQTmN tbl env (QAppE f e) = prettyQTmN tbl env f ++ " " ++ prettyElemAtomN tbl env e
  prettyQTmN tbl env (QAppI f a) = prettyQTmN tbl env f ++ " (" ++ prettyQTmN tbl env a ++ ")"
  prettyQTmN tbl env (QEqC l r u) =
    prettyQTmN tbl env l ++ " ≡ " ++ prettyQTmN tbl env r ++ " ∈ " ++ prettyQTmN tbl env u

  prettyQTyN : FixTable -> NameEnv -> QTy -> String
  prettyQTyN tbl env QU = "U"
  prettyQTyN tbl env (QEl t) = "El (" ++ prettyQTmN tbl env t ++ ")"
  prettyQTyN tbl env (QPiExt a b) =
    "(" ++ prettyTyN tbl env a ++ ") ⇛ " ++ prettyQTyN tbl (env :< wildcard) b
  prettyQTyN tbl env (QPiInd u b) =
    "(" ++ prettyQTmN tbl env u ++ ") ⇛ " ++ prettyQTyN tbl (env :< wildcard) b

  prettyElemAtomN : FixTable -> NameEnv -> Elem -> String
  prettyElemAtomN tbl env (CtxVar n) = nameAt env n
  prettyElemAtomN tbl env OneIntro = "()"
  prettyElemAtomN tbl env NatIntro0 = "Z"
  prettyElemAtomN tbl env Star = "⋆"
  prettyElemAtomN tbl env Elem.ZeroTy = "𝟘"
  prettyElemAtomN tbl env Elem.OneTy = "𝟙"
  prettyElemAtomN tbl env Elem.NatTy = "ℕ"
  prettyElemAtomN tbl env UniverseTy = "𝕌"
  prettyElemAtomN tbl env PropTy = "Ω"
  prettyElemAtomN tbl env TopTy = "𝕍"
  prettyElemAtomN tbl env (Squash t) = "∥" ++ prettyTyN tbl env t ++ "∥"
  prettyElemAtomN tbl env (SigVar x [<]) = sigRefN x
  -- an identity-spine reference at its own context prints bare:
  -- `x`, not `x[n]`
  prettyElemAtomN tbl env (SigVar x es) =
    if isIdSpineN (length env) es
      then sigRefN x
      else sigRefN x ++ "[" ++ prettySubNormN tbl env es ++ "]"
  prettyElemAtomN tbl env (QSort sg k es) = prettyQSortN tbl env sg k es
  prettyElemAtomN tbl env (QCtor sg k es) = "𝒮." ++ show k ++ "[" ++ prettySubNormN tbl env es ++ "]"
  prettyElemAtomN tbl env (QElim sg k ms fs es w) =
    "𝒮." ++ show k ++ "-elim[" ++ prettySubNormN tbl env es ++ "](" ++ prettyElemN tbl env w ++ ")"
  prettyElemAtomN tbl env e = "(" ++ prettyElemN tbl env e ++ ")"

  ||| t˲ ::= ε | t˲ , t — the empty normal substitution prints as nothing
  ||| at all, same as Sub above (e.g. `vect[]`, not `vect[·]`).
  export
  prettySubNormN : FixTable -> NameEnv -> SubNorm -> String
  prettySubNormN tbl env s = fromMaybe "" (prettySubNormElemsN tbl env s)

  prettySubNormElemsN : FixTable -> NameEnv -> SubNorm -> Maybe String
  prettySubNormElemsN tbl env [<] = Nothing
  prettySubNormElemsN tbl env (es :< e) =
    case prettySubNormElemsN tbl env es of
      Nothing   => Just (prettyElemNoCommaN tbl env e)
      Just rest => Just (rest ++ ", " ++ prettyElemNoCommaN tbl env e)

  -- ===== Ty (same mutual block: ∥T∥ embeds a Ty in an Elem) =====

  export
  prettyTyN : FixTable -> NameEnv -> Ty -> String
  prettyTyN tbl env (Elem.EqTy e0 e1 a) =
    -- the equality prop IS the ≡-type (Prf retired)
    prettyElemOpN tbl env 0 e0 ++ " ≡ " ++ prettyElemOpN tbl env 0 e1 ++ " ∈ " ++ prettyTyArrowN tbl env a
  prettyTyN tbl env ty = prettyTyArrowN tbl env ty

  prettyTyArrowN : FixTable -> NameEnv -> Ty -> String
  prettyTyArrowN tbl env (PiTy a b) =
    if usesIndexTy 0 b
      -- Domain sits inside an explicit "(x: ... )" binder, already fully
      -- delimited by the closing paren, so it can be printed unrestricted
      -- (parseTy, not parseTyEl, is what actually parses it back) instead
      -- of forcing another, redundant, pair of parens around it.
      then let x = freshForTy a env
           in "(" ++ x ++ ":" ++ prettyTyN tbl env a ++ ") → " ++ prettyTyArrowN tbl (env :< x) b
      else prettyTyElN tbl env a ++ " → " ++ prettyTyArrowN tbl (env :< wildcard) b
  prettyTyArrowN tbl env (SigmaTy a b) =
    if usesIndexTy 0 b
      then let x = freshForTy a env
           in "(" ++ x ++ ":" ++ prettyTyN tbl env a ++ ") × " ++ prettyTyArrowN tbl (env :< x) b
      else prettyTyElN tbl env a ++ " × " ++ prettyTyArrowN tbl (env :< wildcard) b
  prettyTyArrowN tbl env ty@(SumTy _ _) = prettyTySumN tbl env ty
  prettyTyArrowN tbl env (QuotTy a r) =
    let x = freshForTy a env
        y = freshGeneric (env :< x)
    in prettyTyElN tbl env a ++ " / (" ++ x ++ " " ++ y ++ ". " ++ prettyElemNoCommaN tbl (env :< x :< y) r ++ ")"
  prettyTyArrowN tbl env ty = prettyTyElN tbl env ty

  -- ⊎ binds tighter than → × / (its own level; non-sum components
  -- print at the El level, which parenthesizes looser forms)
  prettyTySumN : FixTable -> NameEnv -> Ty -> String
  prettyTySumN tbl env (SumTy a b) =
    prettyTyElN tbl env a ++ " ⊎ " ++ prettyTySumN tbl env b
  prettyTySumN tbl env ty = prettyTyElN tbl env ty

  prettyTyElN : FixTable -> NameEnv -> Ty -> String
  prettyTyElN tbl env (NuTy f) = "ν " ++ prettyPolyAtomN tbl env f
  prettyTyElN tbl env ty = prettyTyAtomN tbl env ty

  -- Polynomials, by the surface grammar's levels: binders and products
  -- at the top, sums tighter, atoms (𝕏, K t, parens) innermost.
  prettyPolyN : FixTable -> NameEnv -> Poly -> String
  prettyPolyN tbl env (PProd f g) =
    prettyPolySumN tbl env f ++ " × " ++ prettyPolyN tbl env g
  prettyPolyN tbl env (PSigma a f) =
    let x = if usesIndexPoly 0 f then freshGeneric env else wildcard
    in "(" ++ x ++ ":" ++ prettyElemNoCommaN tbl env a ++ ") × " ++ prettyPolyN tbl (env :< x) f
  prettyPolyN tbl env (PPi a f) =
    let x = if usesIndexPoly 0 f then freshGeneric env else wildcard
    in "(" ++ x ++ ":" ++ prettyElemNoCommaN tbl env a ++ ") → " ++ prettyPolyN tbl (env :< x) f
  prettyPolyN tbl env f = prettyPolySumN tbl env f

  prettyPolySumN : FixTable -> NameEnv -> Poly -> String
  prettyPolySumN tbl env (PSum f g) =
    prettyPolyAtomN tbl env f ++ " ⊎ " ++ prettyPolySumN tbl env g
  prettyPolySumN tbl env f = prettyPolyAtomN tbl env f

  prettyPolyAtomN : FixTable -> NameEnv -> Poly -> String
  prettyPolyAtomN tbl env PHole = "𝕏"
  prettyPolyAtomN tbl env (PConst a) = "K " ++ prettyElemAtomN tbl env a
  prettyPolyAtomN tbl env f = "(" ++ prettyPolyN tbl env f ++ ")"

  prettyTyAtomN : FixTable -> NameEnv -> Ty -> String
  prettyTyAtomN tbl env ZeroTy = "𝟘"
  prettyTyAtomN tbl env OneTy = "𝟙"
  prettyTyAtomN tbl env NatTy = "ℕ"
  prettyTyAtomN tbl env UniverseTy = "𝕌"
  prettyTyAtomN tbl env PropTy = "Ω"
  prettyTyAtomN tbl env TopTy = "𝕍"
  prettyTyAtomN tbl env (SigVar x [<]) = sigRefN x
  prettyTyAtomN tbl env (SigVar x es) =
    if isIdSpineN (length env) es
      then sigRefN x
      else sigRefN x ++ "[" ++ prettySubNormN tbl env es ++ "]"
  prettyTyAtomN tbl env (QSort sg k es) = prettyQSortN tbl env sg k es
  -- a non-former type is a CODE (El retired): print it as an element
  -- — recursing into prettyTyN here would loop, since no type clause
  -- will ever match it
  prettyTyAtomN tbl env ty@(PiTy _ _) = "(" ++ prettyTyN tbl env ty ++ ")"
  prettyTyAtomN tbl env ty@(SigmaTy _ _) = "(" ++ prettyTyN tbl env ty ++ ")"
  prettyTyAtomN tbl env ty@(SumTy _ _) = "(" ++ prettyTyN tbl env ty ++ ")"
  prettyTyAtomN tbl env ty@(QuotTy _ _) = "(" ++ prettyTyN tbl env ty ++ ")"
  prettyTyAtomN tbl env ty@(NuTy _) = "(" ++ prettyTyN tbl env ty ++ ")"
  prettyTyAtomN tbl env ty = prettyElemAtomN tbl env ty

-- ===== Ctx =====

||| Print a context, inventing a name for each entry left-to-right, and
||| return the resulting name environment (needed by callers to print
||| whatever this context is the ambient scope for).
export
prettyCtxWithEnv : FixTable -> Ctx -> (String, NameEnv)
prettyCtxWithEnv tbl [<] = ("ε", [<])
prettyCtxWithEnv tbl (rest :< ty) =
  let (restStr, env) = prettyCtxWithEnv tbl rest
      x = freshForTy ty env
  in (restStr ++ " ▷ " ++ x ++ ":" ++ prettyTyN tbl env ty, env :< x)

export
prettyCtxN : FixTable -> Ctx -> String
prettyCtxN tbl ctx = fst (prettyCtxWithEnv tbl ctx)

||| The name environment a context's own entries were invented with —
||| i.e. what to use to print anything stated *in* this context.
export
envForCtx : Ctx -> NameEnv
envForCtx ctx = snd (prettyCtxWithEnv [] ctx)

