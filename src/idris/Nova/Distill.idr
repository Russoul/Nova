module Nova.Distill

-- The DISTILL printer, Phase 1 of docs/NovaPerfectSurface.txt: render
-- a loaded module back to surface text at the IDENTITY sugar tier and
-- verify the round trip.
--
-- The renderer consumes ModUnits — the loader's parsed modules, whose
-- items are the indexed surface ASTs the elaborator consumed — and
-- mirrors the surface grammar of Nova.Elaboration.Parser production by
-- production: every printing level below names the parser production
-- whose operand position it renders into, so a term is parenthesized
-- exactly when the grammar demands it. λ and let additionally SWALLOW
-- everything after themselves (their bodies are maximal), so they
-- print bare only in TRAILING position — when nothing of the
-- enclosing delimited region prints after them.
--
-- Verification (the round-trip harness, docs/NovaPerfectSurface.txt
-- "Phase 1, precisely"): re-parse the rendered modules and require
-- structurally identical ASTs (the range-insensitive Show instances
-- are the comparator), then re-elaborate and require output identical
-- to the original run's. The AST check is the identity-tier contract
-- and relaxes per sugar tier; the elaboration check never relaxes.

import Data.Either
import Data.List
import Data.List1
import Data.Maybe
import Data.String
import Data.SnocList

import Me.Russoul.Text.Range

import Nova.Elaboration
import Nova.Elaboration.Surface
import Nova.Elaboration.Named
import Nova.Elaboration.Parser
import Nova.Elaboration.Loader
import Nova.Profile

import System.Directory
import System.File

%default covering

-- ===== Printing levels =====

||| How an infix operand context treats a child operator of EQUAL
||| precedence (strictly-greater always fits). Precedence climbing is
||| order-sensitive at equal precedence: the left operand of a
||| left-associative operator re-folds correctly only if its own head
||| operator is also left-associative; the right operand of a
||| right-associative operator re-folds correctly whatever the child's
||| associativity; every other equal-precedence pairing must
||| parenthesize.
data EqPol = NoEq | EqIf Assoc | EqAny

||| Element-level printing contexts, one per parser operand position.
data ELvl
  = LPair          -- t{0}: parseSElem (pairs allowed)
  | LNoComma       -- t{1}: parseSElemNoComma
  | LSumC          -- t{1¼}: parseSElemSumC
  | LOp0           -- entry into parseSElemOp (climb 0)
  | LOpBin Nat EqPol -- an infix operand: child op precedence must
                     -- exceed the level, or equal it per the policy
  | LPrefix        -- t{2}: parseSElemPrefix
  | LApp           -- t{3}: parseSElemApp (application/projection head)
  | LAtom          -- t{5}: parseSElemAtom

||| Element node classes, by the production that produces them.
data ECls
  = CPair
  | CNoComma
  | CSumC
  | COp Nat Assoc
  | CPrefix
  | CApp
  | CAtom

fitsE : ECls -> ELvl -> Bool
fitsE CPair lvl = case lvl of LPair => True; _ => False
fitsE CNoComma lvl = case lvl of LPair => True; LNoComma => True; _ => False
fitsE CSumC lvl = case lvl of
  LPair => True; LNoComma => True; LSumC => True; _ => False
fitsE (COp p a) lvl = case lvl of
  LPair => True; LNoComma => True; LSumC => True; LOp0 => True
  LOpBin m pol => p > m || (p == m && ok pol)
  _ => False
 where
  ok : EqPol -> Bool
  ok NoEq = False
  ok (EqIf a') = a == a'
  ok EqAny = True
fitsE CPrefix lvl = case lvl of LApp => False; LAtom => False; _ => True
fitsE CApp lvl = case lvl of LAtom => False; _ => True
fitsE CAtom _ = True

||| Type-level printing contexts (T{0}, T{1}, T{1½}, T{2}, T{4}).
data TLvl = TTop | TArrow | TSum | TEl | TAtom

data TCls = CTTop | CTArrow | CTSum | CTEl | CTAtom

fitsT : TCls -> TLvl -> Bool
fitsT CTTop lvl = case lvl of TTop => True; _ => False
fitsT CTArrow lvl = case lvl of TTop => True; TArrow => True; _ => False
fitsT CTSum lvl = case lvl of
  TTop => True; TArrow => True; TSum => True; _ => False
fitsT CTEl lvl = case lvl of TAtom => False; _ => True
fitsT CTAtom _ = True

||| Polynomial printing contexts (F{0/1}, F{1½}, F{2}).
data PLvl = PTop | PSum | PAtom

data PCls = CPTop | CPSum | CPAtom

fitsP : PCls -> PLvl -> Bool
fitsP CPTop lvl = case lvl of PTop => True; _ => False
fitsP CPSum lvl = case lvl of PTop => True; PSum => True; _ => False
fitsP CPAtom _ = True

-- ===== Name references =====

||| Is the name a single (unqualified) segment?
bareName : String -> Bool
bareName x = not ('.' `elem` unpack x)

||| A signature reference in expression position. An operator-shaped
||| name prints in mention form `(op)` when it could not stand bare: a
||| qualified operator has no bare spelling at all, and a bare operator
||| WITH a fixity in scope is infix-only outside the mention form.
sigRef : FixTable -> String -> String
sigRef tbl x =
  if isOpName x
    then if bareName x
           then case lookup x tbl of
                  Just _ => "(\{x})"
                  Nothing => x
           else "(\{x})"
    else x

||| The infix view of an application node: `l op r` for a bare
||| operator head whose fixity is in scope (such an operator is
||| infix-only, so this is the one legal layout).
infixView : FixTable -> SElem -> Maybe (String, Assoc, Nat, SElem, SElem)
infixView tbl (SApp (SApp (SSig _ op) l) r) =
  if isOpName op && bareName op
    then case lookup op tbl of
           Just (a, p) => Just (op, a, p, l, r)
           Nothing => Nothing
    else Nothing
infixView _ _ = Nothing

-- ===== The renderer =====

mutual
  ||| Class of an element node — which productions can yield it.
  classE : FixTable -> SElem -> ECls
  classE tbl e = case e of
    SPair _ _ => CPair
    SLam _ _ => CPrefix
    SLet _ _ _ => CPrefix
    SPiC _ _ _ => CNoComma
    SSigmaC _ _ _ => CNoComma
    SQuotC _ _ _ _ => CNoComma
    SEqC _ _ _ => CNoComma
    SChain _ _ => CNoComma
    SSumC _ _ => CSumC
    SApp f a => case infixView tbl e of
      Just (_, assoc, p, _, _) => COp p assoc
      Nothing => CApp
    SProj1 _ => CApp
    SProj2 _ => CApp
    SSuc _ => CPrefix
    SZeroElim _ => CPrefix
    SNatElim _ _ _ _ _ _ _ => CPrefix
    SInj1 _ => CPrefix
    SInj2 _ => CPrefix
    SSumElim _ _ _ _ _ _ _ => CPrefix
    SClass _ => CPrefix
    SQuotElim _ _ _ _ _ => CPrefix
    SNuC _ => CPrefix
    SOut _ => CPrefix
    SCorec _ _ _ _ => CPrefix
    SCoind _ _ _ _ _ _ _ _ => CPrefix
    SSquashElim _ _ _ => CPrefix
    SStarWit _ => CPrefix
    SStarUsing _ => CPrefix
    _ => CAtom

  ||| Does the node's parse extend to the end of the enclosing
  ||| delimited region (λ/let bodies are maximal)? Such a node prints
  ||| bare only in trailing position.
  swallows : SElem -> Bool
  swallows (SLam _ _) = True
  swallows (SLet _ _ _) = True
  swallows _ = False

  ||| Render an element into the given context level; `tr` says the
  ||| node is TRAILING — nothing of the enclosing delimited region
  ||| prints after it.
  pe : FixTable -> ELvl -> (tr : Bool) -> SElem -> String
  pe tbl lvl tr e =
    if fitsE (classE tbl e) lvl && (tr || not (swallows e))
      then peRaw tbl tr e
      else "(\{peRaw tbl True e})"

  peRaw : FixTable -> (tr : Bool) -> SElem -> String
  peRaw tbl tr e = case e of
    SPair u v => "\{pe tbl LNoComma False u}, \{pe tbl LPair tr v}"
    SLam (x, _) b => "λ\{x}. \{pe tbl LPair tr b}"
    -- an ascribed definiens prints in the annotated-let form (the two
    -- spellings parse to the same AST)
    SLet (x, _) (SAnn d ty) b =>
      "let \{x} : \{pt tbl TTop True ty} ≔ \{pe tbl LPair True d} in \{pe tbl LPair tr b}"
    SLet (x, _) d b =>
      "let \{x} ≔ \{pe tbl LPair True d} in \{pe tbl LPair tr b}"
    SApp f a => case infixView tbl e of
      Just (op, assoc, p, l, r) =>
        let lctx = case assoc of
                     AssocL => LOpBin p (EqIf AssocL)
                     AssocR => LOpBin p NoEq
            rctx = case assoc of
                     AssocL => LOpBin p NoEq
                     AssocR => LOpBin p EqAny
        in "\{pe tbl lctx False l} \{op} \{pe tbl rctx tr r}"
      Nothing => "\{pe tbl LApp False f} \{pe tbl LAtom False a}"
    SProj1 t => "\{pe tbl LApp False t} .π₁"
    SProj2 t => "\{pe tbl LApp False t} .π₂"
    SSuc t => "S \{pe tbl LAtom False t}"
    SZeroElim t => "𝟘-elim \{pe tbl LAtom False t}"
    SInj1 t => "inj₁ \{pe tbl LAtom False t}"
    SInj2 t => "inj₂ \{pe tbl LAtom False t}"
    SClass t => "class \{pe tbl LAtom False t}"
    SOut t => "out \{pe tbl LAtom False t}"
    SNuC f => "ν \{pp tbl PAtom f}"
    SNatElim (n, _) mot z (n2, _) (ih, _) s t =>
      "ℕ-elim (\{n}. \{pt tbl TTop True mot}) \{pe tbl LAtom False z} " ++
      "(\{n2} \{ih}. \{pe tbl LPair True s}) \{pe tbl LAtom False t}"
    SSumElim (z, _) mot (a, _) l (b, _) r t =>
      "⊎-elim (\{z}. \{pt tbl TTop True mot}) (\{a}. \{pe tbl LPair True l}) " ++
      "(\{b}. \{pe tbl LPair True r}) \{pe tbl LAtom False t}"
    SQuotElim (z, _) mot (a, _) f q =>
      "quot-elim (\{z}. \{pt tbl TTop True mot}) (\{a}. \{pe tbl LPair True f}) " ++
      "\{pe tbl LAtom False q}"
    SCorec (x, _) a f u =>
      "corec (\{x} : \{pe tbl LNoComma True a}. \{pe tbl LPair True f}) \{pe tbl LAtom False u}"
    SCoind (x, _) (y, _) r pw (mx, _) (my, _) (mh, _) q =>
      "coind (\{x} \{y}. \{pe tbl LPair True r}) \{pe tbl LAtom False pw} " ++
      "(\{mx} \{my} \{mh}. \{pe tbl LPair True q})"
    SSquashElim s (x, _) b =>
      "squash-elim \{pe tbl LAtom False s} (\{x}. \{pe tbl LPair True b})"
    SStarWit w => "⋆ \{pe tbl LAtom False w}"
    SStarUsing ns => "⋆ using (\{joinBy ", " ns})"
    SChain h links =>
      pe tbl LSumC False h ++
      concatMap (\(j, m) => " ≡⟨ \{pe tbl LPair True j} ⟩ \{pe tbl LSumC False m}") links
    SEqC l r ty =>
      "\{pe tbl LSumC False l} ≡ \{pe tbl LSumC False r} ∈ \{pt tbl TEl False ty}"
    SSumC a b => "\{pe tbl LOp0 False a} ⊎ \{pe tbl LSumC tr b}"
    SPiC x a b =>
      if x == wildcard
        then "\{pe tbl LSumC False a} → \{pe tbl LNoComma tr b}"
        else piCRun tbl tr ["(\{x} : \{pe tbl LPair True a})"] b
    SSigmaC x a b =>
      if x == wildcard
        then "\{pe tbl LSumC False a} ⨯ \{pe tbl LNoComma tr b}"
        else sigmaCRun tbl tr ["(\{x} : \{pe tbl LPair True a})"] b
    SQuotC a (x, _) (y, _) r =>
      "\{pe tbl LSumC False a} / (\{x} \{y}. \{pe tbl LNoComma True r})"
    SVar _ x _ => x
    SSig _ x => sigRef tbl x
    SUnitI => "()"
    SZeroN => "Z"
    SStar => "⋆"
    SSquash ty => "∥\{pt tbl TTop True ty}∥"
    SZeroC => "𝟘"
    SOneC => "𝟙"
    SNatC => "ℕ"
    SAnn t ty => "(\{pe tbl LPair True t} : \{pt tbl TTop True ty})"

  ||| The 𝕌-code counterpart of `tyPiRun` (parseBinderGroupsC folds
  ||| the same way).
  piCRun : FixTable -> (tr : Bool) -> List String -> SElem -> String
  piCRun tbl tr acc (SPiC x a b) =
    if x /= wildcard
      then piCRun tbl tr (acc ++ ["(\{x} : \{pe tbl LPair True a})"]) b
      else "\{joinBy " " acc} → \{pe tbl LNoComma tr (SPiC x a b)}"
  piCRun tbl tr acc cod = "\{joinBy " " acc} → \{pe tbl LNoComma tr cod}"

  sigmaCRun : FixTable -> (tr : Bool) -> List String -> SElem -> String
  sigmaCRun tbl tr acc (SSigmaC x a b) =
    if x /= wildcard
      then sigmaCRun tbl tr (acc ++ ["(\{x} : \{pe tbl LPair True a})"]) b
      else "\{joinBy " " acc} ⨯ \{pe tbl LNoComma tr (SSigmaC x a b)}"
  sigmaCRun tbl tr acc cod = "\{joinBy " " acc} ⨯ \{pe tbl LNoComma tr cod}"

  classT : STy -> TCls
  classT ty = case ty of
    STyEq _ _ _ => CTTop
    STyPi _ _ _ => CTArrow
    STySigma _ _ _ => CTArrow
    STyQuot _ _ _ _ => CTArrow
    STySum _ _ => CTSum
    STyEl _ => CTEl
    STyPrf _ => CTEl
    STyNu _ => CTEl
    _ => CTAtom

  ||| Render a type into the given context level. Types contain no
  ||| swallowers of their own (a λ inside a type is always behind a
  ||| delimiter the grammar provides), so no trailing flag is needed —
  ||| `tr` is accepted for symmetry with the element printer and to
  ||| keep call sites honest about their positions.
  pt : FixTable -> TLvl -> (tr : Bool) -> STy -> String
  pt tbl lvl tr ty =
    if fitsT (classT ty) lvl
      then ptRaw tbl ty
      else "(\{ptRaw tbl ty})"

  ptRaw : FixTable -> STy -> String
  ptRaw tbl ty = case ty of
    STyEq l r t =>
      "\{pe tbl LOp0 False l} ≡ \{pe tbl LOp0 False r} ∈ \{pt tbl TArrow True t}"
    STyPi x a b =>
      if x == wildcard
        then "\{pt tbl TSum False a} → \{pt tbl TTop True b}"
        else tyPiRun tbl ["(\{x} : \{pt tbl TTop True a})"] b
    STySigma x a b =>
      if x == wildcard
        then "\{pt tbl TSum False a} ⨯ \{pt tbl TTop True b}"
        else tySigmaRun tbl ["(\{x} : \{pt tbl TTop True a})"] b
    STyQuot a (x, _) (y, _) r =>
      "\{pt tbl TSum False a} / (\{x} \{y}. \{pe tbl LNoComma True r})"
    STySum a b => "\{pt tbl TEl False a} ⊎ \{pt tbl TSum False b}"
    STyEl e => "El \{pe tbl LAtom False e}"
    STyPrf e => "Prf \{pe tbl LAtom False e}"
    STyNu f => "ν \{pp tbl PAtom f}"
    STySig x => x
    STyZero => "𝟘"
    STyOne => "𝟙"
    STyNat => "ℕ"
    STyUniv => "𝕌"
    STyProp => "Ω"

  ||| Compact a run of consecutively NAMED Π-binders into one binder
  ||| group — `(x : A) (y : B) → C` — the corpus idiom; the grouped
  ||| and arrow-chained spellings parse to the same AST.
  tyPiRun : FixTable -> List String -> STy -> String
  tyPiRun tbl acc (STyPi x a b) =
    if x /= wildcard
      then tyPiRun tbl (acc ++ ["(\{x} : \{pt tbl TTop True a})"]) b
      else "\{joinBy " " acc} → \{pt tbl TTop True (STyPi x a b)}"
  tyPiRun tbl acc cod = "\{joinBy " " acc} → \{pt tbl TTop True cod}"

  tySigmaRun : FixTable -> List String -> STy -> String
  tySigmaRun tbl acc (STySigma x a b) =
    if x /= wildcard
      then tySigmaRun tbl (acc ++ ["(\{x} : \{pt tbl TTop True a})"]) b
      else "\{joinBy " " acc} ⨯ \{pt tbl TTop True (STySigma x a b)}"
  tySigmaRun tbl acc cod = "\{joinBy " " acc} ⨯ \{pt tbl TTop True cod}"

  classP : SPoly -> PCls
  classP f = case f of
    SPProd _ _ => CPTop
    SPSigma _ _ _ => CPTop
    SPPi _ _ _ => CPTop
    SPSum _ _ => CPSum
    _ => CPAtom

  pp : FixTable -> PLvl -> SPoly -> String
  pp tbl lvl f =
    if fitsP (classP f) lvl
      then ppRaw tbl f
      else "(\{ppRaw tbl f})"

  ppRaw : FixTable -> SPoly -> String
  ppRaw tbl f = case f of
    SPProd g h => "\{pp tbl PSum g} ⨯ \{pp tbl PTop h}"
    SPSigma (x, _) a g => "(\{x} : \{pe tbl LNoComma True a}) ⨯ \{pp tbl PTop g}"
    SPPi (x, _) a g => "(\{x} : \{pe tbl LNoComma True a}) → \{pp tbl PTop g}"
    SPSum g h => "\{pp tbl PAtom g} ⊎ \{pp tbl PSum h}"
    SPHole => "𝕏"
    SPConst a => "K \{pe tbl LAtom False a}"

-- ===== QIIT literals =====

||| A ToS chain; `atom` demands an atom (parenthesize applications).
pq : FixTable -> (atom : Bool) -> SQTm -> String
pq tbl atom t = case t of
  SQVar n _ => n
  _ => if atom then "(\{go t})" else go t
 where
  go : SQTm -> String
  go (SQVar n _) = n
  go (SQAppE f a) = "\{go f} \{pe tbl LAtom False a}"
  go (SQAppI f (SQVar n _)) = "\{go f} \{n}"
  go (SQAppI f a) = "\{go f} (\{go a})"

renderQRes : FixTable -> SQRes -> String
renderQRes tbl SQResU = "U"
renderQRes tbl (SQResEl q) = "El \{pq tbl True q}"
renderQRes tbl (SQResEq l r u) =
  "\{pq tbl False l} ≡ \{pq tbl False r} ∈ El \{pq tbl True u}"

renderQDomain : FixTable -> Either STy SQTm -> String
renderQDomain tbl (Left ty) = pt tbl TTop True ty
renderQDomain tbl (Right q) = "El \{pq tbl True q}"

||| Anonymous domains stand bare (the external case at T{2} —
||| sqDomainNoArrow); named binders group like every binder telescope:
||| a run of consecutive named binders shares one arrow.
renderQBinders : FixTable -> List (String, Either STy SQTm) -> String
renderQBinders tbl [] = ""
renderQBinders tbl bs@((x, d) :: rest) =
  if x == wildcard
    then (case d of
            Left ty => "\{pt tbl TEl False ty} → "
            Right q => "El \{pq tbl True q} → ") ++ renderQBinders tbl rest
    else let (run, more) = span (\(y, _) => y /= wildcard) bs in
         joinBy " " (map (\(y, dom) => "(\{y} : \{renderQDomain tbl dom})") run)
           ++ " → " ++ renderQBinders tbl more

renderQDecl : FixTable -> SQDecl -> String
renderQDecl tbl (MkSQDecl n bs res) =
  "\{n} : " ++ renderQBinders tbl bs ++ renderQRes tbl res

-- ===== Clauses =====

mutual
  renderPat : SPat -> String
  renderPat (SPVar (x, _)) = x
  renderPat SPZero = "Z"
  renderPat (SPSuc p) = "S \{renderPatAtom p}"
  renderPat (SPInj1 p) = "inj₁ \{renderPatAtom p}"
  renderPat (SPInj2 p) = "inj₂ \{renderPatAtom p}"

  renderPatAtom : SPat -> String
  renderPatAtom p = case p of
    SPVar (x, _) => x
    SPZero => "Z"
    _ => "(\{renderPat p})"

renderClause : FixTable -> String -> SClause -> String
renderClause tbl iname (MkSClause pats _ rhs mn) =
  let lhs = case (isOpName iname, pats) of
              -- an operator-named item's two-pattern clause lays out
              -- infix (the corpus spelling); operands sit at full
              -- pattern level there
              (True, [p1, p2]) => "\{renderPat p1} \{iname} \{renderPat p2}"
              (True, _) => joinBy " " ("(\{iname})" :: map renderPatAtom pats)
              (False, _) => joinBy " " (iname :: map renderPatAtom pats)
  in "| \{lhs} ≔ \{pe tbl LPair True rhs}" ++
     maybe "" (\n => " [\{n}]") mn

-- ===== Items, fixities, imports, modules =====

renderUsing : Maybe (List String) -> String
renderUsing Nothing = ""
renderUsing (Just ns) = " using (\{joinBy ", " ns})"

||| Break a long body's calc chains at their links. Justifications are
||| never chains themselves (a ⋆-family link is a structural error), so
||| every ` ≡⟨ ` in a rendered body opens a link of some chain, and a
||| uniform indent re-parses identically (whitespace is transparent).
breakChains : String -> String
breakChains s = pack (go (unpack s))
 where
  go : List Char -> List Char
  go (' ' :: '≡' :: '⟨' :: rest) = unpack "\n    ≡⟨" ++ go rest
  go (c :: rest) = c :: go rest
  go [] = []

||| Break a long definition after ≔ (readability only — whitespace is
||| transparent to the round trip).
withBody : (header : String) -> (body : String) -> String
withBody hdr body =
  if length hdr + length body + 3 <= 110
    then "\{hdr} ≔ \{body}"
    else "\{hdr} ≔\n  \{breakChains body}"

renderItem : FixTable -> SItem -> String
renderItem tbl (SDef n ty body mu) =
  withBody "def \{n} : \{pt tbl TTop False ty}\{renderUsing mu}" (pe tbl LPair True body)
renderItem tbl (SDeclDef _ n ty) = "def \{n} : \{pt tbl TTop False ty}"
renderItem tbl (STypeDef n ty) = "type \{n} ≔ \{pt tbl TTop True ty}"
renderItem tbl (SData params ds) =
  "data " ++ concatMap (\(x, t) => "[\{x} : \{pt tbl TTop True t}] ") params ++
  (case ds of
     [d] => "( \{renderQDecl tbl d} )"
     _ => "( " ++ joinBy "\n     ; " (map (renderQDecl tbl) ds) ++ " )")
renderItem tbl (SClausalDef _ n ty eta wit cls) =
  "def \{n} : \{pt tbl TTop False ty}" ++
  maybe "" (\e => " [\{e}]") eta ++
  maybe "" (\w => " ≔ \{pe tbl LPair True w}") wit ++
  concatMap (\c => "\n  \{renderClause tbl n c}") cls

renderFixity : SFixity -> String
renderFixity (op, AssocL, d) = "infixl \{show d} \{op}"
renderFixity (op, AssocR, d) = "infixr \{show d} \{op}"

renderImport : SImport -> String
renderImport (MkSImport m []) = "import \{m}"
renderImport (MkSImport m os) = "import \{m} (\{joinBy ", " os})"

||| Render a whole module: imports, then the body in source order.
export
renderUnit : ModUnit -> String
renderUnit u =
  let imps = map renderImport u.mimports
      body = map (either renderFixity (renderItem u.mfix . snd)) u.mbody
  in joinBy "\n" (imps ++ (case imps of [] => []; _ => [""]) ++ body) ++ "\n"

-- ===== Round-trip verification =====

fixShow : SFixity -> String
fixShow (op, AssocL, d) = "\{op}/l/\{show d}"
fixShow (op, AssocR, d) = "\{op}/r/\{show d}"

||| Structural comparison of an original and a re-parsed module, via
||| the range-insensitive Show instances. Identity-tier contract only
||| (docs/NovaPerfectSurface.txt): later sugar tiers relax this check,
||| never the elaboration check.
verifyUnit : ModUnit -> ModUnit -> Maybe String
verifyUnit orig re =
  if orig.mname /= re.mname
    then Just "module order mismatch: '\{orig.mname}' vs '\{re.mname}'"
  else if map show orig.mimports /= map show re.mimports
    then Just "module \{orig.mname}: imports differ after distill"
  else if map fixShow (lefts orig.mbody) /= map fixShow (lefts re.mbody)
    then Just "module \{orig.mname}: fixity declarations differ after distill"
  else go (map snd (rights orig.mbody)) (map snd (rights re.mbody))
 where
  go : List SItem -> List SItem -> Maybe String
  go [] [] = Nothing
  go (i :: is) [] = Just "module \{orig.mname}: item '\{itemName i}' lost in distill"
  go [] (i :: _) = Just "module \{orig.mname}: item '\{itemName i}' appeared from nowhere"
  go (i :: is) (j :: js) =
    if show i == show j
      then go is js
      else Just $ "module \{orig.mname}: item '\{itemName i}' changed under distill\n" ++
                  "  original:  \{show i}\n" ++
                  "  reparsed:  \{show j}"

verifyUnits : List ModUnit -> List ModUnit -> Maybe String
verifyUnits [] [] = Nothing
verifyUnits (u :: us) (v :: vs) =
  case verifyUnit u v of
    Just err => Just err
    Nothing => verifyUnits us vs
verifyUnits us vs = Just "module count differs after distill (\{show (length us)} vs \{show (length vs)})"

-- ===== IO driver =====

baseName : String -> String
baseName path =
  case reverse (forget (split (== '/') path)) of
    (b :: _) => b
    [] => path

||| Strip trailing slashes for a plain-string directory comparison.
normDir : String -> String
normDir d =
  case reverse (unpack d) of
    ('/' :: rest) => normDir (pack (reverse rest))
    _ => d

||| Create outDir and the intermediate directories a dotted module
||| name needs (import A.B ⇝ outDir/A/B.nova).
ensureDirs : String -> (mname : String) -> IO ()
ensureDirs outDir mname = do
  ignore (createDir outDir)
  let segs = forget (split (== '.') mname)
  go outDir (dropLast segs)
 where
  dropLast : List String -> List String
  dropLast [] = []
  dropLast [_] = []
  dropLast (s :: ss) = s :: dropLast ss

  go : String -> List String -> IO ()
  go _ [] = pure ()
  go base (s :: ss) = do
    let d = base ++ "/" ++ s
    ignore (createDir d)
    go d ss

unitPath : (outDir : String) -> (rootBase : String) -> ModUnit -> String
unitPath outDir rootBase u =
  if u.mname == "" then outDir ++ "/" ++ rootBase else modPath outDir u.mname

writeUnits : (outDir : String) -> (rootBase : String) -> List ModUnit -> IO (Either String ())
writeUnits outDir rootBase [] = pure (Right ())
writeUnits outDir rootBase (u :: us) = do
  ensureDirs outDir u.mname
  let path = unitPath outDir rootBase u
  Right () <- writeFile path (renderUnit u)
    | Left err => pure (Left "cannot write '\{path}': \{show err}")
  writeUnits outDir rootBase us

countItems : List ModUnit -> Nat
countItems = sum . map (length . mitems)

||| The `nova distill` command body: load and elaborate the root's
||| closure (input must be accepted), render every module into outDir,
||| then verify the round trip — re-parsed ASTs structurally identical,
||| re-elaboration output identical (docs/NovaPerfectSurface.txt,
||| "Phase 1, precisely").
export
distillPath : (rootPath : String) -> (outDir : String) -> IO (Either String String)
distillPath rootPath outDir = do
  Right units <- loadProgram rootPath
    | Left err => pure (Left err.lmsg)
  let out1 = elabProgram units
  let True = isSuffixOf "Accepted." out1
    | False => pure (Left ("input is not accepted; distill only transforms accepted programs:\n" ++ out1))
  let False = normDir (dirOf rootPath) == normDir outDir
    | True => pure (Left "output directory equals the source directory; refusing to overwrite sources")
  Right () <- writeUnits outDir (baseName rootPath) units
    | Left err => pure (Left err)
  Right units' <- loadProgram (outDir ++ "/" ++ baseName rootPath)
    | Left err => pure (Left ("distilled output failed to load: " ++ err.lmsg))
  let Nothing = verifyUnits units units'
    | Just err => pure (Left err)
  let out2 = elabProgram units'
  let True = out1 == out2
    | False => pure (Left ("distilled elaboration differs from the original run:\n" ++ out2))
  pure (Right ("distilled \{show (length units)} modules (\{show (countItems units)} items) to \{outDir}\n" ++
               "round-trip OK: ASTs identical, elaboration identical."))
