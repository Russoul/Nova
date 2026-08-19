module Nova.Distill

-- The DISTILL printer, Phases 1–2 of docs/NovaPerfectSurface.txt:
-- render a loaded module back to surface text and verify the round
-- trip.
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
-- Phase 2 (the bijective tier) adds: numerals for ground S-towers,
-- multi-name binder groups ((x y : A) → — recognized by shift-equal
-- domains, undoing exactly the parser's weakening desugar), and a
-- layout engine (a small Wadler/Oppen Doc: group = try flat, break
-- otherwise). All of it is AST-bijective, so the identity-tier
-- verification below is unchanged.
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

-- ===== The layout engine =====
--
-- A minimal Wadler/Oppen pretty-printer: DLine is a soft break (a
-- space when its innermost group fits the line, a newline + indent
-- otherwise), DHard always breaks (and forces every enclosing group
-- broken), DNest adds indent to the breaks inside it. Whitespace is
-- transparent to the parser, so layout never affects the round trip.

data Doc
  = DNil
  | DText String
  | DCat Doc Doc
  | DLine
  | DHard
  | DGroup Doc
  | DNest Nat Doc

infixr 6 <->

(<->) : Doc -> Doc -> Doc
(<->) = DCat

txt : String -> Doc
txt = DText

data DMode = MFlat | MBroken

fitsD : Int -> List (Nat, DMode, Doc) -> Bool
fitsD rem xs =
  if rem < 0 then False else case xs of
    [] => True
    ((i, m, DNil) :: z) => fitsD rem z
    ((i, m, DText s) :: z) => fitsD (rem - cast (length s)) z
    ((i, m, DCat a b) :: z) => fitsD rem ((i, m, a) :: (i, m, b) :: z)
    ((i, m, DNest j a) :: z) => fitsD rem ((i + j, m, a) :: z)
    ((i, MFlat, DLine) :: z) => fitsD (rem - 1) z
    ((i, MBroken, DLine) :: z) => True
    ((i, MFlat, DHard) :: z) => False
    ((i, MBroken, DHard) :: z) => True
    ((i, m, DGroup a) :: z) => fitsD rem ((i, MFlat, a) :: z)

renderDoc : (width : Nat) -> Doc -> String
renderDoc w doc = fastConcat (go 0 [(0, MBroken, doc)])
 where
  go : Nat -> List (Nat, DMode, Doc) -> List String
  go col [] = []
  go col ((i, m, DNil) :: z) = go col z
  go col ((i, m, DText s) :: z) = s :: go (col + length s) z
  go col ((i, m, DCat a b) :: z) = go col ((i, m, a) :: (i, m, b) :: z)
  go col ((i, m, DNest j a) :: z) = go col ((i + j, m, a) :: z)
  go col ((i, MFlat, DLine) :: z) = " " :: go (S col) z
  go col ((i, MBroken, DLine) :: z) = ("\n" ++ replicate i ' ') :: go i z
  go col ((i, m, DHard) :: z) = ("\n" ++ replicate i ' ') :: go i z
  go col ((i, m, DGroup a) :: z) =
    if fitsD (cast w - cast col) ((i, MFlat, a) :: z)
      then go col ((i, MFlat, a) :: z)
      else go col ((i, MBroken, a) :: z)

lineWidth : Nat
lineWidth = 100

dparen : Doc -> Doc
dparen d = txt "(" <-> d <-> txt ")"

||| A soft break point that indents its continuation.
brk : Doc -> Doc
brk d = DGroup (DNest 2 (DLine <-> d))

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

||| A ground S-tower's value; numerals print for values ≥ 2 (Z and S Z
||| stay structural — the corpus idiom — while towers print as the
||| decimal the parser reads back to the same AST).
natView : SElem -> Maybe Nat
natView SZeroN = Just 0
natView (SSuc t) = map S (natView t)
natView _ = Nothing

numeralView : SElem -> Maybe Nat
numeralView e = case natView e of
  Just n => if n >= 2 then Just n else Nothing
  Nothing => Nothing

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
    SSuc _ => case numeralView e of
      Just _ => CAtom
      Nothing => CPrefix
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
  pe : FixTable -> ELvl -> (tr : Bool) -> SElem -> Doc
  pe tbl lvl tr e =
    if fitsE (classE tbl e) lvl && (tr || not (swallows e))
      then peRaw tbl tr e
      else dparen (peRaw tbl True e)

  peRaw : FixTable -> (tr : Bool) -> SElem -> Doc
  peRaw tbl tr e = case e of
    SPair u v => pe tbl LNoComma False u <-> txt "," <-> brk (pe tbl LPair tr v)
    SLam (x, _) b => txt "λ\{x}. " <-> pe tbl LPair tr b
    -- an ascribed definiens prints in the annotated-let form (the two
    -- spellings parse to the same AST)
    SLet (x, _) (SAnn d ty) b =>
      txt "let \{x} : " <-> pt tbl TTop True ty <-> txt " ≔ " <->
      pe tbl LPair True d <-> txt " in " <-> pe tbl LPair tr b
    SLet (x, _) d b =>
      txt "let \{x} ≔ " <-> pe tbl LPair True d <-> txt " in " <-> pe tbl LPair tr b
    SApp f a => case infixView tbl e of
      Just (op, assoc, p, l, r) =>
        let lctx = case assoc of
                     AssocL => LOpBin p (EqIf AssocL)
                     AssocR => LOpBin p NoEq
            rctx = case assoc of
                     AssocL => LOpBin p NoEq
                     AssocR => LOpBin p EqAny
        in pe tbl lctx False l <-> DGroup (DNest 2 (DLine <-> txt "\{op} " <-> pe tbl rctx tr r))
      Nothing =>
        -- flatten the spine: one group, every argument at the same
        -- break level (an overlong call breaks one-argument-per-line
        -- at a uniform indent, never a staircase)
        let (h, args) = spineView tbl e in
        DGroup (pe tbl LApp False h <->
                DNest 2 (concatDoc (map (\arg => DLine <-> pe tbl LAtom False arg) args)))
    SProj1 t => pe tbl LApp False t <-> txt " .π₁"
    SProj2 t => pe tbl LApp False t <-> txt " .π₂"
    SSuc t => case numeralView e of
      Just n => txt (show n)
      Nothing => txt "S " <-> pe tbl LAtom False t
    SZeroElim t => txt "𝟘-elim " <-> pe tbl LAtom False t
    SInj1 t => txt "inj₁ " <-> pe tbl LAtom False t
    SInj2 t => txt "inj₂ " <-> pe tbl LAtom False t
    SClass t => txt "class " <-> pe tbl LAtom False t
    SOut t => txt "out " <-> pe tbl LAtom False t
    SNuC f => txt "ν " <-> pp tbl PAtom f
    SNatElim (n, _) mot z (n2, _) (ih, _) s t =>
      DGroup (txt "ℕ-elim (\{n}. " <-> pt tbl TTop True mot <-> txt ")" <->
              DNest 2 (DLine <-> pe tbl LAtom False z <->
                       DLine <-> txt "(\{n2} \{ih}. " <-> pe tbl LPair True s <-> txt ")" <->
                       DLine <-> pe tbl LAtom False t))
    SSumElim (z, _) mot (a, _) l (b, _) r t =>
      DGroup (txt "⊎-elim (\{z}. " <-> pt tbl TTop True mot <-> txt ")" <->
              DNest 2 (DLine <-> txt "(\{a}. " <-> pe tbl LPair True l <-> txt ")" <->
                       DLine <-> txt "(\{b}. " <-> pe tbl LPair True r <-> txt ")" <->
                       DLine <-> pe tbl LAtom False t))
    SQuotElim (z, _) mot (a, _) f q =>
      DGroup (txt "quot-elim (\{z}. " <-> pt tbl TTop True mot <-> txt ")" <->
              DNest 2 (DLine <-> txt "(\{a}. " <-> pe tbl LPair True f <-> txt ")" <->
                       DLine <-> pe tbl LAtom False q))
    SCorec (x, _) a f u =>
      txt "corec (\{x} : " <-> pe tbl LNoComma True a <-> txt ". " <->
      pe tbl LPair True f <-> txt ") " <-> pe tbl LAtom False u
    SCoind (x, _) (y, _) r pw (mx, _) (my, _) (mh, _) q =>
      DGroup (txt "coind (\{x} \{y}. " <-> pe tbl LPair True r <-> txt ")" <->
              DNest 2 (DLine <-> pe tbl LAtom False pw <->
                       DLine <-> txt "(\{mx} \{my} \{mh}. " <-> pe tbl LPair True q <-> txt ")"))
    SSquashElim s (x, _) b =>
      txt "squash-elim " <-> pe tbl LAtom False s <-> txt " (\{x}. " <->
      pe tbl LPair True b <-> txt ")"
    SStarWit w => txt "⋆ " <-> pe tbl LAtom False w
    SStarUsing ns => txt "⋆ using (" <-> usingNames ns <-> txt ")"
    SChain h links =>
      DGroup (pe tbl LSumC False h <->
              concatDoc (map (\(j, m) => DNest 4 (DLine <-> txt "≡⟨ " <-> pe tbl LPair True j <->
                                                  txt " ⟩ " <-> pe tbl LSumC False m)) links))
    SEqC l r ty =>
      pe tbl LSumC False l <-> txt " ≡ " <-> pe tbl LSumC False r <->
      txt " ∈ " <-> pt tbl TEl False ty
    SSumC a b => pe tbl LOp0 False a <-> txt " ⊎ " <-> pe tbl LSumC tr b
    SPiC x a b =>
      if x == wildcard
        then pe tbl LSumC False a <-> txt " → " <-> pe tbl LNoComma tr b
        else piCRun tbl tr [(x, a)] b
    SSigmaC x a b =>
      if x == wildcard
        then pe tbl LSumC False a <-> txt " ⨯ " <-> pe tbl LNoComma tr b
        else sigmaCRun tbl tr [(x, a)] b
    SQuotC a (x, _) (y, _) r =>
      pe tbl LSumC False a <-> txt " / (\{x} \{y}. " <-> pe tbl LNoComma True r <-> txt ")"
    SVar _ x _ => txt x
    SSig _ x => txt (sigRef tbl x)
    SUnitI => txt "()"
    SZeroN => txt "Z"
    SStar => txt "⋆"
    SSquash ty => txt "∥" <-> pt tbl TTop True ty <-> txt "∥"
    SZeroC => txt "𝟘"
    SOneC => txt "𝟙"
    SNatC => txt "ℕ"
    SAnn t ty => dparen (pe tbl LPair True t <-> txt " : " <-> pt tbl TTop True ty)

  concatDoc : List Doc -> Doc
  concatDoc = foldr DCat DNil

  ||| Unfold an application chain to (head, arguments); stops at any
  ||| non-application head and at an infix node (which prints as an
  ||| operator expression, parenthesized by its class).
  spineView : FixTable -> SElem -> (SElem, List SElem)
  spineView tbl e = go e []
   where
    go : SElem -> List SElem -> (SElem, List SElem)
    go (SApp f a) acc = case infixView tbl (SApp f a) of
      Just _ => (SApp f a, acc)
      Nothing => go f (a :: acc)
    go h acc = (h, acc)

  ||| Coalesce a telescope run into groups of shift-equal domains —
  ||| `(x y : A)` — undoing the parser's weakening desugar exactly
  ||| (the range-insensitive Show is the comparator, so a hand-written
  ||| `(x : A) (y : A)` with the right indices groups too).
  coalesceTys : List (String, STy) -> List (List String, STy)
  coalesceTys [] = []
  coalesceTys ((x, a) :: rest) = go [x] a a rest
   where
    go : List String -> STy -> STy -> List (String, STy) -> List (List String, STy)
    go names first prev ((y, b) :: more) =
      if show b == show (shiftTy 0 prev)
        then go (names ++ [y]) first b more
        else (names, first) :: coalesceTys ((y, b) :: more)
    go names first prev [] = [(names, first)]

  coalesceElems : List (String, SElem) -> List (List String, SElem)
  coalesceElems [] = []
  coalesceElems ((x, a) :: rest) = go [x] a a rest
   where
    go : List String -> SElem -> SElem -> List (String, SElem) -> List (List String, SElem)
    go names first prev ((y, b) :: more) =
      if show b == show (shiftElem 0 prev)
        then go (names ++ [y]) first b more
        else (names, first) :: coalesceElems ((y, b) :: more)
    go names first prev [] = [(names, first)]

  ||| Compact a run of consecutively NAMED Π-binders into binder
  ||| groups — `(x y : A) (z : B) → C` — the corpus idiom; the
  ||| grouped and arrow-chained spellings parse to the same AST.
  tyPiRun : FixTable -> List (String, STy) -> STy -> Doc
  tyPiRun tbl acc (STyPi x a b) =
    if x /= wildcard
      then tyPiRun tbl (acc ++ [(x, a)]) b
      else tyRunEnd tbl "→" acc (STyPi x a b)
  tyPiRun tbl acc cod = tyRunEnd tbl "→" acc cod

  tySigmaRun : FixTable -> List (String, STy) -> STy -> Doc
  tySigmaRun tbl acc (STySigma x a b) =
    if x /= wildcard
      then tySigmaRun tbl (acc ++ [(x, a)]) b
      else tyRunEnd tbl "⨯" acc (STySigma x a b)
  tySigmaRun tbl acc cod = tyRunEnd tbl "⨯" acc cod

  tyRunEnd : FixTable -> (arrow : String) -> List (String, STy) -> STy -> Doc
  tyRunEnd tbl arrow acc cod =
    -- ONE group over the whole telescope: a long telescope breaks at
    -- its binder seams (all of them, uniformly indented), which also
    -- localizes every domain-internal fits scan to its own binder
    let groups = map (\(ns, a) => dparen (txt (joinBy " " ns) <-> txt " : " <-> pt tbl TTop True a))
                     (coalesceTys acc)
    in DGroup (concatDoc (intersperse (DNest 2 DLine) groups) <->
               DNest 2 (DLine <-> txt "\{arrow} " <-> pt tbl TTop True cod))

  ||| The 𝕌-code counterpart (parseBinderGroupsC folds the same way).
  piCRun : FixTable -> (tr : Bool) -> List (String, SElem) -> SElem -> Doc
  piCRun tbl tr acc (SPiC x a b) =
    if x /= wildcard
      then piCRun tbl tr (acc ++ [(x, a)]) b
      else cRunEnd tbl tr "→" acc (SPiC x a b)
  piCRun tbl tr acc cod = cRunEnd tbl tr "→" acc cod

  sigmaCRun : FixTable -> (tr : Bool) -> List (String, SElem) -> SElem -> Doc
  sigmaCRun tbl tr acc (SSigmaC x a b) =
    if x /= wildcard
      then sigmaCRun tbl tr (acc ++ [(x, a)]) b
      else cRunEnd tbl tr "⨯" acc (SSigmaC x a b)
  sigmaCRun tbl tr acc cod = cRunEnd tbl tr "⨯" acc cod

  cRunEnd : FixTable -> (tr : Bool) -> (arrow : String) -> List (String, SElem) -> SElem -> Doc
  cRunEnd tbl tr arrow acc cod =
    let groups = map (\(ns, a) => dparen (txt (joinBy " " ns) <-> txt " : " <-> pe tbl LPair True a))
                     (coalesceElems acc)
    in DGroup (concatDoc (intersperse (DNest 2 DLine) groups) <->
               DNest 2 (DLine <-> txt "\{arrow} " <-> pe tbl LNoComma tr cod))

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
  pt : FixTable -> TLvl -> (tr : Bool) -> STy -> Doc
  pt tbl lvl tr ty =
    if fitsT (classT ty) lvl
      then ptRaw tbl ty
      else dparen (ptRaw tbl ty)

  ptRaw : FixTable -> STy -> Doc
  ptRaw tbl ty = case ty of
    STyEq l r t =>
      pe tbl LOp0 False l <-> txt " ≡ " <-> pe tbl LOp0 False r <->
      txt " ∈ " <-> pt tbl TArrow True t
    STyPi x a b =>
      if x == wildcard
        then pt tbl TSum False a <-> DGroup (DNest 2 (DLine <-> txt "→ " <-> pt tbl TTop True b))
        else tyPiRun tbl [(x, a)] b
    STySigma x a b =>
      if x == wildcard
        then pt tbl TSum False a <-> DGroup (DNest 2 (DLine <-> txt "⨯ " <-> pt tbl TTop True b))
        else tySigmaRun tbl [(x, a)] b
    STyQuot a (x, _) (y, _) r =>
      pt tbl TSum False a <-> txt " / (\{x} \{y}. " <-> pe tbl LNoComma True r <-> txt ")"
    STySum a b => pt tbl TEl False a <-> txt " ⊎ " <-> pt tbl TSum False b
    STyEl e => txt "El " <-> pe tbl LAtom False e
    STyPrf e => txt "Prf " <-> pe tbl LAtom False e
    STyNu f => txt "ν " <-> pp tbl PAtom f
    STySig x => txt x
    STyZero => txt "𝟘"
    STyOne => txt "𝟙"
    STyNat => txt "ℕ"
    STyUniv => txt "𝕌"
    STyProp => txt "Ω"

  classP : SPoly -> PCls
  classP f = case f of
    SPProd _ _ => CPTop
    SPSigma _ _ _ => CPTop
    SPPi _ _ _ => CPTop
    SPSum _ _ => CPSum
    _ => CPAtom

  pp : FixTable -> PLvl -> SPoly -> Doc
  pp tbl lvl f =
    if fitsP (classP f) lvl
      then ppRaw tbl f
      else dparen (ppRaw tbl f)

  ppRaw : FixTable -> SPoly -> Doc
  ppRaw tbl f = case f of
    SPProd g h => pp tbl PSum g <-> txt " ⨯ " <-> pp tbl PTop h
    SPSigma (x, _) a g =>
      dparen (txt "\{x} : " <-> pe tbl LNoComma True a) <-> txt " ⨯ " <-> pp tbl PTop g
    SPPi (x, _) a g =>
      dparen (txt "\{x} : " <-> pe tbl LNoComma True a) <-> txt " → " <-> pp tbl PTop g
    SPSum g h => pp tbl PAtom g <-> txt " ⊎ " <-> pp tbl PSum h
    SPHole => txt "𝕏"
    SPConst a => txt "K " <-> pe tbl LAtom False a

  ||| A using-name list: soft-breaks after commas.
  usingNames : List String -> Doc
  usingNames ns =
    DGroup (DNest 2 (concatDoc (intersperse (txt "," <-> DLine) (map txt ns))))

-- ===== QIIT literals =====

||| A ToS chain; `atom` demands an atom (parenthesize applications).
pq : FixTable -> (atom : Bool) -> SQTm -> Doc
pq tbl atom t = case t of
  SQVar n _ => txt n
  _ => if atom then dparen (go t) else go t
 where
  go : SQTm -> Doc
  go (SQVar n _) = txt n
  go (SQAppE f a) = go f <-> txt " " <-> pe tbl LAtom False a
  go (SQAppI f (SQVar n _)) = go f <-> txt " \{n}"
  go (SQAppI f a) = go f <-> txt " " <-> dparen (go a)

renderQRes : FixTable -> SQRes -> Doc
renderQRes tbl SQResU = txt "U"
renderQRes tbl (SQResEl q) = txt "El " <-> pq tbl True q
renderQRes tbl (SQResEq l r u) =
  pq tbl False l <-> txt " ≡ " <-> pq tbl False r <-> txt " ∈ El " <-> pq tbl True u

renderQDomain : FixTable -> Either STy SQTm -> Doc
renderQDomain tbl (Left ty) = pt tbl TTop True ty
renderQDomain tbl (Right q) = txt "El " <-> pq tbl True q

||| Anonymous domains stand bare (the external case at T{2} —
||| sqDomainNoArrow); named binders group like every binder telescope:
||| a run of consecutive named binders shares one arrow.
renderQBinders : FixTable -> List (String, Either STy SQTm) -> Doc
renderQBinders tbl [] = DNil
renderQBinders tbl bs@((x, d) :: rest) =
  if x == wildcard
    then (case d of
            Left ty => pt tbl TEl False ty
            Right q => txt "El " <-> pq tbl True q) <-> txt " → " <-> renderQBinders tbl rest
    else let (run, more) = span (\(y, _) => y /= wildcard) bs in
         concatDoc (intersperse (txt " ")
             (map (\(y, dom) => dparen (txt "\{y} : " <-> renderQDomain tbl dom)) run))
           <-> txt " → " <-> renderQBinders tbl more

renderQDecl : FixTable -> SQDecl -> Doc
renderQDecl tbl (MkSQDecl n bs res) =
  txt "\{n} : " <-> renderQBinders tbl bs <-> renderQRes tbl res

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

renderClause : FixTable -> String -> SClause -> Doc
renderClause tbl iname (MkSClause pats _ rhs mn) =
  let lhs = case (isOpName iname, pats) of
              -- an operator-named item's two-pattern clause lays out
              -- infix (the corpus spelling); operands sit at full
              -- pattern level there
              (True, [p1, p2]) => "\{renderPat p1} \{iname} \{renderPat p2}"
              (True, _) => joinBy " " ("(\{iname})" :: map renderPatAtom pats)
              (False, _) => joinBy " " (iname :: map renderPatAtom pats)
  in txt "| \{lhs} ≔ " <-> pe tbl LPair True rhs <->
     (case mn of
        Nothing => DNil
        Just n => txt " [\{n}]")

-- ===== Items, fixities, imports, modules =====

concatD : List Doc -> Doc
concatD = foldr DCat DNil

renderUsing : Maybe (List String) -> Doc
renderUsing Nothing = DNil
renderUsing (Just ns) = txt " using (" <-> usingNames ns <-> txt ")"

||| The flat (single-line) width of a document; a hard break never
||| fits flat.
flatW : Doc -> Nat
flatW DNil = 0
flatW (DText s) = length s
flatW (DCat a b) = flatW a + flatW b
flatW DLine = 1
flatW DHard = 100000
flatW (DGroup d) = flatW d
flatW (DNest _ d) = flatW d

||| Lay out `header ≔ body` with the SEAM decided first: if the whole
||| item fits one line, render flat; otherwise the body moves under
||| the header at indent 2, and each half is laid out against the
||| width ALONE. (A single linear document would let the body pollute
||| the fits scan of every group inside the type — the greedy engine
||| would break at an arrow when the natural break is the ≔.)
seam : (header : Doc) -> (body : Doc) -> String
seam hdr bod =
  if flatW hdr + 1 + flatW bod <= lineWidth
    then renderDoc lineWidth (hdr <-> txt " " <-> bod)
    else renderDoc lineWidth hdr ++ "\n" ++
         renderDoc lineWidth (DNest 2 (txt "  " <-> bod))

renderItem : FixTable -> SItem -> Doc
renderItem tbl (SDef n ty body mu) =
  -- unreachable through renderItemStr (kept total for other callers)
  txt "def \{n} : " <-> pt tbl TTop False ty <-> renderUsing mu <->
  txt " ≔" <-> DGroup (DNest 2 (DLine <-> pe tbl LPair True body))
renderItem tbl (SDeclDef _ n ty) = txt "def \{n} : " <-> pt tbl TTop False ty
renderItem tbl (STypeDef n ty) = txt "type \{n} ≔ " <-> pt tbl TTop True ty
renderItem tbl (SData params ds) =
  txt "data " <->
  concatD (map (\(x, t) => txt "[\{x} : " <-> pt tbl TTop True t <-> txt "] ") params) <->
  (case ds of
     [d] => txt "( " <-> renderQDecl tbl d <-> txt " )"
     _ => txt "( " <->
          concatD (intersperse (DNest 5 DHard <-> txt "; ") (map (renderQDecl tbl) ds)) <->
          txt " )")
renderItem tbl (SClausalDef _ n ty eta wit cls) =
  txt "def \{n} : " <-> pt tbl TTop False ty <->
  (case eta of
     Nothing => DNil
     Just e => txt " [\{e}]") <->
  (case wit of
     Nothing => DNil
     Just w => txt " ≔ " <-> pe tbl LPair True w) <->
  concatD (map (\c => DNest 2 (DHard <-> renderClause tbl n c)) cls)

renderItemStr : FixTable -> SItem -> String
renderItemStr tbl (SDef n ty body mu) =
  let tyPart = txt "def \{n} : " <-> pt tbl TTop False ty
      usePart = renderUsing mu
      bod = pe tbl LPair True body
  in if flatW tyPart + flatW usePart + 3 + flatW bod <= lineWidth
       -- everything on one line
       then renderDoc lineWidth (tyPart <-> usePart <-> txt " ≔ " <-> bod)
     else if flatW tyPart + flatW usePart + 2 <= lineWidth
       -- header on one line, body below
       then renderDoc lineWidth (tyPart <-> usePart <-> txt " ≔") ++ "\n" ++
            renderDoc lineWidth (DNest 2 (txt "  " <-> bod))
     else case mu of
       -- the using clause gets its own line (breaking names at
       -- commas if still long); the type lays out against the width
       -- ALONE, so its telescope seams fire only for its own length
       Just ns =>
         renderDoc lineWidth tyPart ++ "\n" ++
         renderDoc lineWidth (DNest 2 (txt "  using (" <-> usingNames ns <-> txt ") ≔")) ++ "\n" ++
         renderDoc lineWidth (DNest 2 (txt "  " <-> bod))
       Nothing =>
         renderDoc lineWidth (tyPart <-> txt " ≔") ++ "\n" ++
         renderDoc lineWidth (DNest 2 (txt "  " <-> bod))
renderItemStr tbl (STypeDef n ty) =
  seam (txt "type \{n} ≔") (pt tbl TTop True ty)
renderItemStr tbl item = renderDoc lineWidth (renderItem tbl item)

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
      body = map (either renderFixity (renderItemStr u.mfix . snd)) u.mbody
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
