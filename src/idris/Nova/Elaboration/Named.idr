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
-- (dropping the name entirely) instead of `(x : A) → B`/`(x : A) × B`: if the
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

||| An application spine, split into its head and its arguments in
||| written order. The head is never itself a `PiApp`.
spineViewN : Elem -> (Elem, List Elem)
spineViewN (PiApp f e) = let (hd, args) = spineViewN f in (hd, args ++ [e])
spineViewN e = (e, [])

||| The implicit positions of an application's head, when it is a bare
||| Σ reference the run recorded any for. Only a reference at the EMPTY
||| declaration context qualifies: `impls` records the leading
||| Π-telescope of an ITEM's type, and those are the only entries whose
||| telescope positions line up with a spine's arguments.
headImpsN : ImpTable -> Elem -> Maybe (List Nat)
headImpsN imps (SigVar x [<]) = case lookup x imps of
  Just (p :: ps) => Just (p :: ps)
  _ => Nothing
headImpsN _ _ = Nothing

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
  prettySubN : ImpTable -> FixTable -> NameEnv -> Sub -> String
  prettySubN imps tbl env s = fromMaybe "" (prettySubElemsN imps tbl env s)

  -- Nothing = no elements printed yet (the empty/Terminal case); Just str
  -- = the rendered comma-separated element list so far. Id/Wk/Chain can
  -- never be constructed by any rule in this grammar anymore (see
  -- NamedParser.idr's header) — reaching one here means a real bug
  -- upstream (e.g. something bypassed the named parser/checker), so this
  -- crashes loudly rather than silently printing an unreparseable string.
  prettySubElemsN : ImpTable -> FixTable -> NameEnv -> Sub -> Maybe String
  prettySubElemsN imps tbl env (Ext s e) =
    case prettySubElemsN imps tbl env s of
      Nothing   => Just (prettyElemNoCommaN imps tbl env e)
      Just rest => Just (rest ++ ", " ++ prettyElemNoCommaN imps tbl env e)
  prettySubElemsN imps tbl env Terminal = Nothing
  prettySubElemsN imps tbl env Id = assert_total (idris_crash "prettySubN: unreachable Id (no rule constructs it)")
  prettySubElemsN imps tbl env Wk = assert_total (idris_crash "prettySubN: unreachable Wk (no rule constructs it)")
  prettySubElemsN imps tbl env (Chain _ _) = assert_total (idris_crash "prettySubN: unreachable Chain (no rule constructs it)")

  export
  prettyElemN : ImpTable -> FixTable -> NameEnv -> Elem -> String
  prettyElemN imps tbl env (SigmaIntro e e') = prettyElemNoCommaN imps tbl env e ++ ", " ++ prettyElemN imps tbl env e'
  prettyElemN imps tbl env e = prettyElemNoCommaN imps tbl env e

  export
  prettyElemNoCommaN : ImpTable -> FixTable -> NameEnv -> Elem -> String
  prettyElemNoCommaN imps tbl env (Elem.PiTy e e') =
    if usesIndexElem 0 e'
      -- Domain sits inside an explicit "(x : ...)" binder, already fully
      -- delimited by the closing paren, so it can be printed unrestricted
      -- (parseElem, not parseElemPrefix, is what actually parses it back)
      -- instead of forcing another, redundant, pair of parens around it.
      then let x = freshGeneric env
           in "(" ++ x ++ " : " ++ prettyElemN imps tbl env e ++ ") → " ++ prettyElemNoCommaN imps tbl (env :< x) e'
      else prettyElemOpN imps tbl env 0 e ++ " → " ++ prettyElemNoCommaN imps tbl (env :< wildcard) e'
  prettyElemNoCommaN imps tbl env (Elem.SigmaTy e e') =
    if usesIndexElem 0 e'
      then let x = freshGeneric env
           in "(" ++ x ++ " : " ++ prettyElemN imps tbl env e ++ ") × " ++ prettyElemNoCommaN imps tbl (env :< x) e'
      else prettyElemOpN imps tbl env 0 e ++ " × " ++ prettyElemNoCommaN imps tbl (env :< wildcard) e'
  prettyElemNoCommaN imps tbl env e@(Elem.SumTy _ _) = prettyElemSumN imps tbl env e
  prettyElemNoCommaN imps tbl env (Elem.EqTy e0 e1 t2) =
    prettyElemOpN imps tbl env 0 e0 ++ " ≡ " ++ prettyElemOpN imps tbl env 0 e1 ++ " ∈ " ++ prettyTyArrowN imps tbl env t2
  prettyElemNoCommaN imps tbl env (QuotTy e r) =
    let x = freshForTy e env
        y = freshGeneric (env :< x)
    in prettyElemOpN imps tbl env 0 e ++ " / (" ++ x ++ " " ++ y ++ ". " ++ prettyElemNoCommaN imps tbl (env :< x :< y) r ++ ")"
  prettyElemNoCommaN imps tbl env e = prettyElemOpN imps tbl env 0 e

  -- the ⊎ code binds tighter than the other infix element formers
  -- (chain at its own level; any non-sum component prints at the
  -- operator level, which parenthesizes arrows and pairs)
  prettyElemSumN : ImpTable -> FixTable -> NameEnv -> Elem -> String
  prettyElemSumN imps tbl env (Elem.SumTy e e') =
    prettyElemOpN imps tbl env 0 e ++ " ⊎ " ++ prettyElemSumN imps tbl env e'
  prettyElemSumN imps tbl env e = prettyElemOpN imps tbl env 0 e

  -- t{1½}: operator applications, precedence-aware — parenthesized
  -- exactly when the operator binds looser than the context demands.
  -- An operator with no fixity in scope falls through to the prefix
  -- spelling ((+) a b), which is always valid.
  prettyElemOpN : ImpTable -> FixTable -> NameEnv -> (minPrec : Nat) -> Elem -> String
  prettyElemOpN imps tbl env minP e@(PiApp (PiApp (SigVar op [<]) a) b) =
    -- fixity keys the OPENED bare token, Σ-names are qualified: a
    -- reference like prop.⊃ finds its fixity (and lays out) by its
    -- last segment — the spelling the source used.
    --
    -- The two arguments a spine of this shape carries stand at
    -- telescope positions 0 and 1, and an infix layout has nowhere to
    -- put a `{t}` override: if either is IMPLICIT the operator lays out
    -- as the prefix application the surface would have to write.
    case (isOpName op, lookup op tbl <|> lookup (lastSeg op) tbl,
          any (\q => q == 0 || q == 1) (fromMaybe [] (headImpsN imps (SigVar op [<])))) of
      (True, Just (assoc, p), False) =>
        let lP = case assoc of AssocL => p; AssocR => S p
            rP = case assoc of AssocL => S p; AssocR => p
            body = prettyElemOpN imps tbl env lP a ++ " " ++ lastSeg op ++ " " ++ prettyElemOpN imps tbl env rP b
        in if p < minP then "(" ++ body ++ ")" else body
      _ => prettyElemPrefixN imps tbl env e
  prettyElemOpN imps tbl env minP e = prettyElemPrefixN imps tbl env e

  prettyElemPrefixN : ImpTable -> FixTable -> NameEnv -> Elem -> String
  prettyElemPrefixN imps tbl env (PiIntro e) =
    let x = freshGeneric env
    in "λ" ++ x ++ ". " ++ prettyElemOpN imps tbl (env :< x) 0 e
  prettyElemPrefixN imps tbl env (Let a b) =
    -- surface-faithful: the unfolding-equation binder has no surface
    -- spelling and elaborator-produced bodies never reference it; it
    -- still enters the env (under a fresh Prf-flavored name) so a
    -- reference in hand-built core would at least print visibly
    let x = freshGeneric env
        h = freshFromList candidatesPrf (env :< x)
    in "let " ++ x ++ " ≔ " ++ prettyElemN imps tbl env a ++ " in "
         ++ prettyElemOpN imps tbl (env :< x :< h) 0 b
  prettyElemPrefixN imps tbl env (ZeroElim e) = "𝟘-elim " ++ prettyElemAtomN imps tbl env e
  prettyElemPrefixN imps tbl env (NatIntro1 e) = "S " ++ prettyElemAtomN imps tbl env e
  prettyElemPrefixN imps tbl env (NatElim z s t) =
    let n  = freshFromList candidatesNat env
        ih = freshIH (env :< n)
    in "ℕ-elim " ++ prettyElemAtomN imps tbl env z ++
       " (" ++ n ++ " " ++ ih ++ ". " ++ prettyElemAtomN imps tbl (env :< n :< ih) s ++ ") " ++
       prettyElemAtomN imps tbl env t
  prettyElemPrefixN imps tbl env (Inj1 a) = "inj₁ " ++ prettyElemAtomN imps tbl env a
  prettyElemPrefixN imps tbl env (Inj2 a) = "inj₂ " ++ prettyElemAtomN imps tbl env a
  prettyElemPrefixN imps tbl env (SumElim l r t) =
    let a = if usesIndexElem 0 l then freshGeneric env else wildcard
        b = if usesIndexElem 0 r then freshGeneric env else wildcard
    in "⊎-elim (" ++ a ++ ". " ++ prettyElemN imps tbl (env :< a) l ++ ") ("
         ++ b ++ ". " ++ prettyElemN imps tbl (env :< b) r ++ ") "
         ++ prettyElemAtomN imps tbl env t
  prettyElemPrefixN imps tbl env (Class a) = "class " ++ prettyElemAtomN imps tbl env a
  prettyElemPrefixN imps tbl env (Elem.NuTy f) = "ν " ++ prettyPolyAtomN imps tbl env f
  prettyElemPrefixN imps tbl env (Out t) = "out " ++ prettyElemAtomN imps tbl env t
  prettyElemPrefixN imps tbl env (Corec p a f x) =
    -- surface-faithful: the carried 𝔽 is not printed (it is the
    -- expected ν-type's, recovered at checking)
    let v = if usesIndexElem 0 f then freshGeneric env else wildcard
    in "corec (" ++ v ++ " : " ++ prettyElemNoCommaN imps tbl env a ++ ". "
         ++ prettyElemN imps tbl (env :< v) f ++ ") " ++ prettyElemAtomN imps tbl env x
  prettyElemPrefixN imps tbl env (QuotElim f q) =
    let a = if usesIndexElem 0 f then freshGeneric env else wildcard
    in "quot-elim (" ++ a ++ ". " ++ prettyElemN imps tbl (env :< a) f ++ ") " ++ prettyElemAtomN imps tbl env q
  prettyElemPrefixN imps tbl env e = prettyElemPostfixN imps tbl env e

  prettyElemPostfixN : ImpTable -> FixTable -> NameEnv -> Elem -> String
  prettyElemPostfixN imps tbl env (SigmaElim1 e) = prettyElemPostfixN imps tbl env e ++ " .π₁"
  prettyElemPostfixN imps tbl env (SigmaElim2 e) = prettyElemPostfixN imps tbl env e ++ " .π₂"
  -- An application spine is printed HEAD-FIRST, so that the arguments
  -- the elaborator INSERTED can be told apart from the ones the
  -- operator wrote: the core is bare, but the head's Σ-name knows its
  -- implicit positions, and each one prints back as the `{t}` override
  -- the surface would have to spell (docs/NovaPerfectSurface.txt,
  -- Phase 3). Eliding them instead would hide the very instantiation a
  -- goal is read to understand.
  prettyElemPostfixN imps tbl env e@(PiApp _ _) =
    let (hd, args) = spineViewN e in
    case headImpsN imps hd of
      Nothing => prettyElemPostfixN imps tbl env hd ++
                   concat (map (\a => " " ++ prettyElemAtomN imps tbl env a) args)
      Just ps => prettyElemPostfixN imps tbl env hd ++
                   concat (zipWith (argAt ps) [0 .. length args] args)
   where
    -- an implicit argument sits inside its own braces, so it prints
    -- unrestricted — the same latitude the distiller gives a written
    -- override
    argAt : List Nat -> Nat -> Elem -> String
    argAt ps i a =
      if i `elem` ps
        then " {" ++ prettyElemN imps tbl env a ++ "}"
        else " " ++ prettyElemAtomN imps tbl env a
  prettyElemPostfixN imps tbl env e = prettyElemAtomN imps tbl env e

  export
  ||| A QIIT sort, signature spelled out: `𝒮{U; (El ℕ) ⇛ ⬡0; …}.k[ē]`
  ||| — the signature is the sort's IDENTITY (structural, nameless),
  ||| so a diagnostic naming only `𝒮.k` hides exactly the part two
  ||| mismatched sorts differ in (an instantiated parameter, say).
  prettyQSortN : ImpTable -> FixTable -> NameEnv -> QSig -> Nat -> SubNorm -> String
  prettyQSortN imps tbl env sg k es =
    "𝒮{" ++ concat (intersperse "; " (map (prettyQTyN imps tbl env) sg)) ++ "}." ++ show k ++
    "[" ++ prettySubNormN imps tbl env es ++ "]"

  prettyQTmN : ImpTable -> FixTable -> NameEnv -> QTm -> String
  prettyQTmN imps tbl env (QVar i) = "⬡" ++ show i
  prettyQTmN imps tbl env (QAppE f e) = prettyQTmN imps tbl env f ++ " " ++ prettyElemAtomN imps tbl env e
  prettyQTmN imps tbl env (QAppI f a) = prettyQTmN imps tbl env f ++ " (" ++ prettyQTmN imps tbl env a ++ ")"
  prettyQTmN imps tbl env (QEqC l r u) =
    prettyQTmN imps tbl env l ++ " ≡ " ++ prettyQTmN imps tbl env r ++ " ∈ " ++ prettyQTmN imps tbl env u

  prettyQTyN : ImpTable -> FixTable -> NameEnv -> QTy -> String
  prettyQTyN imps tbl env QU = "U"
  prettyQTyN imps tbl env (QEl t) = "El (" ++ prettyQTmN imps tbl env t ++ ")"
  prettyQTyN imps tbl env (QPiExt a b) =
    "(" ++ prettyTyN imps tbl env a ++ ") ⇛ " ++ prettyQTyN imps tbl (env :< wildcard) b
  prettyQTyN imps tbl env (QPiInd u b) =
    "(" ++ prettyQTmN imps tbl env u ++ ") ⇛ " ++ prettyQTyN imps tbl (env :< wildcard) b

  prettyElemAtomN : ImpTable -> FixTable -> NameEnv -> Elem -> String
  prettyElemAtomN imps tbl env (CtxVar n) = nameAt env n
  prettyElemAtomN imps tbl env OneIntro = "()"
  prettyElemAtomN imps tbl env NatIntro0 = "Z"
  prettyElemAtomN imps tbl env Star = "⋆"
  prettyElemAtomN imps tbl env Elem.ZeroTy = "𝟘"
  prettyElemAtomN imps tbl env Elem.OneTy = "𝟙"
  prettyElemAtomN imps tbl env Elem.NatTy = "ℕ"
  prettyElemAtomN imps tbl env UniverseTy = "𝕌"
  prettyElemAtomN imps tbl env PropTy = "Ω"
  prettyElemAtomN imps tbl env TopTy = "𝕍"
  prettyElemAtomN imps tbl env (Squash t) = "∥" ++ prettyTyN imps tbl env t ++ "∥"
  prettyElemAtomN imps tbl env (SigVar x [<]) = sigRefN x
  -- an identity-spine reference at its own context prints bare:
  -- `x`, not `x[n]`
  prettyElemAtomN imps tbl env (SigVar x es) =
    if isIdSpineN (length env) es
      then sigRefN x
      else sigRefN x ++ "[" ++ prettySubNormN imps tbl env es ++ "]"
  prettyElemAtomN imps tbl env (QSort sg k es) = prettyQSortN imps tbl env sg k es
  prettyElemAtomN imps tbl env (QCtor sg k es) = "𝒮." ++ show k ++ "[" ++ prettySubNormN imps tbl env es ++ "]"
  prettyElemAtomN imps tbl env (QElim sg k ms fs es w) =
    "𝒮." ++ show k ++ "-elim[" ++ prettySubNormN imps tbl env es ++ "](" ++ prettyElemN imps tbl env w ++ ")"
  prettyElemAtomN imps tbl env e = "(" ++ prettyElemN imps tbl env e ++ ")"

  ||| t˲ ::= ε | t˲ , t — the empty normal substitution prints as nothing
  ||| at all, same as Sub above (e.g. `vect[]`, not `vect[·]`).
  export
  prettySubNormN : ImpTable -> FixTable -> NameEnv -> SubNorm -> String
  prettySubNormN imps tbl env s = fromMaybe "" (prettySubNormElemsN imps tbl env s)

  prettySubNormElemsN : ImpTable -> FixTable -> NameEnv -> SubNorm -> Maybe String
  prettySubNormElemsN imps tbl env [<] = Nothing
  prettySubNormElemsN imps tbl env (es :< e) =
    case prettySubNormElemsN imps tbl env es of
      Nothing   => Just (prettyElemNoCommaN imps tbl env e)
      Just rest => Just (rest ++ ", " ++ prettyElemNoCommaN imps tbl env e)

  -- ===== Ty (same mutual block: ∥T∥ embeds a Ty in an Elem) =====

  export
  prettyTyN : ImpTable -> FixTable -> NameEnv -> Ty -> String
  prettyTyN imps tbl env (Elem.EqTy e0 e1 a) =
    -- the equality prop IS the ≡-type (Prf retired)
    prettyElemOpN imps tbl env 0 e0 ++ " ≡ " ++ prettyElemOpN imps tbl env 0 e1 ++ " ∈ " ++ prettyTyArrowN imps tbl env a
  prettyTyN imps tbl env ty = prettyTyArrowN imps tbl env ty

  prettyTyArrowN : ImpTable -> FixTable -> NameEnv -> Ty -> String
  prettyTyArrowN imps tbl env (PiTy a b) =
    if usesIndexTy 0 b
      -- Domain sits inside an explicit "(x : ...)" binder, already fully
      -- delimited by the closing paren, so it can be printed unrestricted
      -- (parseTy, not parseTyEl, is what actually parses it back) instead
      -- of forcing another, redundant, pair of parens around it.
      then let x = freshForTy a env
           in "(" ++ x ++ " : " ++ prettyTyN imps tbl env a ++ ") → " ++ prettyTyArrowN imps tbl (env :< x) b
      else prettyTyElN imps tbl env a ++ " → " ++ prettyTyArrowN imps tbl (env :< wildcard) b
  prettyTyArrowN imps tbl env (SigmaTy a b) =
    if usesIndexTy 0 b
      then let x = freshForTy a env
           in "(" ++ x ++ " : " ++ prettyTyN imps tbl env a ++ ") × " ++ prettyTyArrowN imps tbl (env :< x) b
      else prettyTyElN imps tbl env a ++ " × " ++ prettyTyArrowN imps tbl (env :< wildcard) b
  prettyTyArrowN imps tbl env ty@(SumTy _ _) = prettyTySumN imps tbl env ty
  prettyTyArrowN imps tbl env (QuotTy a r) =
    let x = freshForTy a env
        y = freshGeneric (env :< x)
    in prettyTyElN imps tbl env a ++ " / (" ++ x ++ " " ++ y ++ ". " ++ prettyElemNoCommaN imps tbl (env :< x :< y) r ++ ")"
  -- An UNRESTRICTED position (a goal, a binder group's domain, a
  -- codomain): a code that is no type former prints as the ELEMENT it
  -- is, at the operator level. The atom level would wrap it in parens
  -- the surrounding grammar already provides — `(s : (stream a))` for
  -- what the source wrote as `stream a`.
  prettyTyArrowN imps tbl env ty = prettyElemOpN imps tbl env 0 ty

  -- ⊎ binds tighter than → × / (its own level; non-sum components
  -- print at the El level, which parenthesizes looser forms)
  prettyTySumN : ImpTable -> FixTable -> NameEnv -> Ty -> String
  prettyTySumN imps tbl env (SumTy a b) =
    prettyTyElN imps tbl env a ++ " ⊎ " ++ prettyTySumN imps tbl env b
  prettyTySumN imps tbl env ty = prettyTyElN imps tbl env ty

  prettyTyElN : ImpTable -> FixTable -> NameEnv -> Ty -> String
  prettyTyElN imps tbl env (NuTy f) = "ν " ++ prettyPolyAtomN imps tbl env f
  prettyTyElN imps tbl env ty = prettyTyAtomN imps tbl env ty

  -- Polynomials, by the surface grammar's levels: binders and products
  -- at the top, sums tighter, atoms (𝕏, K t, parens) innermost.
  prettyPolyN : ImpTable -> FixTable -> NameEnv -> Poly -> String
  prettyPolyN imps tbl env (PProd f g) =
    prettyPolySumN imps tbl env f ++ " × " ++ prettyPolyN imps tbl env g
  prettyPolyN imps tbl env (PSigma a f) =
    let x = if usesIndexPoly 0 f then freshGeneric env else wildcard
    in "(" ++ x ++ " : " ++ prettyElemNoCommaN imps tbl env a ++ ") × " ++ prettyPolyN imps tbl (env :< x) f
  prettyPolyN imps tbl env (PPi a f) =
    let x = if usesIndexPoly 0 f then freshGeneric env else wildcard
    in "(" ++ x ++ " : " ++ prettyElemNoCommaN imps tbl env a ++ ") → " ++ prettyPolyN imps tbl (env :< x) f
  prettyPolyN imps tbl env f = prettyPolySumN imps tbl env f

  prettyPolySumN : ImpTable -> FixTable -> NameEnv -> Poly -> String
  prettyPolySumN imps tbl env (PSum f g) =
    prettyPolyAtomN imps tbl env f ++ " ⊎ " ++ prettyPolySumN imps tbl env g
  prettyPolySumN imps tbl env f = prettyPolyAtomN imps tbl env f

  prettyPolyAtomN : ImpTable -> FixTable -> NameEnv -> Poly -> String
  prettyPolyAtomN imps tbl env PHole = "𝕏"
  prettyPolyAtomN imps tbl env (PConst a) = "K " ++ prettyElemAtomN imps tbl env a
  prettyPolyAtomN imps tbl env f = "(" ++ prettyPolyN imps tbl env f ++ ")"

  prettyTyAtomN : ImpTable -> FixTable -> NameEnv -> Ty -> String
  prettyTyAtomN imps tbl env ZeroTy = "𝟘"
  prettyTyAtomN imps tbl env OneTy = "𝟙"
  prettyTyAtomN imps tbl env NatTy = "ℕ"
  prettyTyAtomN imps tbl env UniverseTy = "𝕌"
  prettyTyAtomN imps tbl env PropTy = "Ω"
  prettyTyAtomN imps tbl env TopTy = "𝕍"
  prettyTyAtomN imps tbl env (SigVar x [<]) = sigRefN x
  prettyTyAtomN imps tbl env (SigVar x es) =
    if isIdSpineN (length env) es
      then sigRefN x
      else sigRefN x ++ "[" ++ prettySubNormN imps tbl env es ++ "]"
  prettyTyAtomN imps tbl env (QSort sg k es) = prettyQSortN imps tbl env sg k es
  -- a non-former type is a CODE (El retired): print it as an element
  -- — recursing into prettyTyN here would loop, since no type clause
  -- will ever match it
  prettyTyAtomN imps tbl env ty@(PiTy _ _) = "(" ++ prettyTyN imps tbl env ty ++ ")"
  prettyTyAtomN imps tbl env ty@(SigmaTy _ _) = "(" ++ prettyTyN imps tbl env ty ++ ")"
  prettyTyAtomN imps tbl env ty@(SumTy _ _) = "(" ++ prettyTyN imps tbl env ty ++ ")"
  prettyTyAtomN imps tbl env ty@(QuotTy _ _) = "(" ++ prettyTyN imps tbl env ty ++ ")"
  prettyTyAtomN imps tbl env ty@(NuTy _) = "(" ++ prettyTyN imps tbl env ty ++ ")"
  -- reached only from `prettyTyElN`, i.e. at the El level — tighter
  -- than → × ⊎ /, but LOOSER than application. So a spine prints bare
  -- here too: `stream a → a`, the way the source wrote it, not
  -- `(stream a) → a`.
  prettyTyAtomN imps tbl env ty = prettyElemPostfixN imps tbl env ty

-- ===== Ctx =====

||| Print a context, inventing a name for each entry left-to-right, and
||| return the resulting name environment (needed by callers to print
||| whatever this context is the ambient scope for).
export
prettyCtxWithEnv : ImpTable -> FixTable -> Ctx -> (String, NameEnv)
prettyCtxWithEnv imps tbl [<] = ("ε", [<])
prettyCtxWithEnv imps tbl (rest :< ty) =
  let (restStr, env) = prettyCtxWithEnv imps tbl rest
      x = freshForTy ty env
  in (restStr ++ " ▷ " ++ x ++ ":" ++ prettyTyN imps tbl env ty, env :< x)

export
prettyCtxN : ImpTable -> FixTable -> Ctx -> String
prettyCtxN imps tbl ctx = fst (prettyCtxWithEnv imps tbl ctx)

||| The name environment a context's own entries were invented with —
||| i.e. what to use to print anything stated *in* this context.
export
envForCtx : Ctx -> NameEnv
envForCtx ctx = snd (prettyCtxWithEnv [] [] ctx)

