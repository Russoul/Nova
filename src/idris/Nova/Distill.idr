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

import Me.Russoul.Text.Position
import Me.Russoul.Text.Range

import Nova.Elaboration
import Nova.Elaboration.Surface
import Nova.Kernel.Parser
import Nova.Kernel.Syntax
import Nova.Elaboration.Named
import Nova.Elaboration.Parser
import Nova.Elaboration.Loader
import Nova.Profile

import System.Directory
import System.File

import Nova.Elaboration.Beta

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

isOverride : SElem -> Bool
isOverride (SImpArg _) = True
isOverride _ = False

||| The infix view of an application node: `l op r` for a bare
||| operator head whose fixity is in scope (such an operator is
||| infix-only, so this is the one legal layout).
infixView : FixTable -> SElem -> Maybe (String, Assoc, Nat, SElem, SElem)
infixView tbl (SApp (SApp (SSig _ op) l) r) =
  if isOpName op && bareName op && not (isOverride l) && not (isOverride r)
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
    SEqC _ _ _ _ => CNoComma
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
    SNatElim _ _ _ _ _ _ => CPrefix
    SInj1 _ => CPrefix
    SInj2 _ => CPrefix
    SSumElim _ _ _ _ _ _ => CPrefix
    SClass _ => CPrefix
    SQuotElim _ _ _ _ => CPrefix
    SNuC _ => CPrefix
    SOut _ => CPrefix
    SCorec _ _ _ _ => CPrefix
    SCoind _ _ _ _ _ _ _ _ => CPrefix
    SSquashElim _ _ _ => CPrefix
    SStarWit _ => CPrefix
    SStarUsing _ _ => CPrefix
    SImpArg _ => CAtom
    SNoIns _ => CApp
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
    SNatElim mot z (n2, _) (ih, _) s t =>
      DGroup (txt "ℕ-elim" <-> motDoc tbl mot <->
              DNest 2 (DLine <-> pe tbl LAtom False z <->
                       DLine <-> txt "(\{n2} \{ih}. " <-> pe tbl LPair True s <-> txt ")" <->
                       DLine <-> pe tbl LAtom False t))
    SSumElim mot (a, _) l (b, _) r t =>
      DGroup (txt "⊎-elim" <-> motDoc tbl mot <->
              DNest 2 (DLine <-> txt "(\{a}. " <-> pe tbl LPair True l <-> txt ")" <->
                       DLine <-> txt "(\{b}. " <-> pe tbl LPair True r <-> txt ")" <->
                       DLine <-> pe tbl LAtom False t))
    SQuotElim mot (a, _) f q =>
      DGroup (txt "quot-elim" <-> motDoc tbl mot <->
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
    SStarUsing _ ns => txt "⋆ using (" <-> usingNames ns <-> txt ")"
    SChain h links =>
      DGroup (pe tbl LSumC False h <->
              concatDoc (map (\(j, m) => DNest 4 (DLine <-> txt "≡⟨ " <-> pe tbl LPair True j <->
                                                  txt " ⟩ " <-> pe tbl LSumC False m)) links))
    SEqC _ l r mty =>
      pe tbl LSumC False l <-> txt " ≡ " <-> eqSide tbl mty r <->
      (case mty of
         Just ty => txt " ∈ " <-> pt tbl TEl False ty
         Nothing => DNil)
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
    SStar _ => txt "⋆"
    SSquash ty => txt "∥" <-> pt tbl TTop True ty <-> txt "∥"
    SZeroC => txt "𝟘"
    SOneC => txt "𝟙"
    SNatC => txt "ℕ"
    SAnn t ty => dparen (pe tbl LPair True t <-> txt " : " <-> pt tbl TTop True ty)
    SImpArg t => txt "{" <-> pe tbl LPair True t <-> txt "}"
    SNoIns t => pe tbl LApp False t <-> txt " {}"
    SBlank _ => txt "_"

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
  ||| `(x : A) (y : A)` with the right indices groups too). Groups
  ||| never mix implicit and explicit binders.
  coalesceTys : List (Bool, String, STy) -> List (Bool, List String, STy)
  coalesceTys [] = []
  coalesceTys ((imp, x, a) :: rest) = go [x] a a rest
   where
    go : List String -> STy -> STy -> List (Bool, String, STy) -> List (Bool, List String, STy)
    go names first prev ((imp', y, b) :: more) =
      if imp' == imp && show b == show (shiftTy 0 prev)
        then go (names ++ [y]) first b more
        else (imp, names, first) :: coalesceTys ((imp', y, b) :: more)
    go names first prev [] = [(imp, names, first)]

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
  ||| Π-runs collect implicit binders too ({x : A} — always named;
  ||| a wildcard EXPLICIT binder ends the run as the name-dropped
  ||| arrow form).
  tyPiRun : FixTable -> List (Bool, String, STy) -> STy -> Doc
  tyPiRun tbl acc (STyPi x a b) =
    if x /= wildcard
      then tyPiRun tbl (acc ++ [(False, x, a)]) b
      else tyRunEnd tbl "→" acc (STyPi x a b)
  tyPiRun tbl acc (STyImpPi x a b) = tyPiRun tbl (acc ++ [(True, x, a)]) b
  tyPiRun tbl acc cod = tyRunEnd tbl "→" acc cod

  tySigmaRun : FixTable -> List (Bool, String, STy) -> STy -> Doc
  tySigmaRun tbl acc (STySigma x a b) =
    if x /= wildcard
      then tySigmaRun tbl (acc ++ [(False, x, a)]) b
      else tyRunEnd tbl "⨯" acc (STySigma x a b)
  tySigmaRun tbl acc cod = tyRunEnd tbl "⨯" acc cod

  tyRunEnd : FixTable -> (arrow : String) -> List (Bool, String, STy) -> STy -> Doc
  tyRunEnd tbl arrow acc cod =
    -- ONE group over the whole telescope: a long telescope breaks at
    -- its binder seams (all of them, uniformly indented), which also
    -- localizes every domain-internal fits scan to its own binder
    let groups = map (\(imp, ns, a) =>
                       let inner = txt (joinBy " " ns) <-> txt " : " <-> pt tbl TTop True a in
                       if imp then txt "{" <-> inner <-> txt "}" else dparen inner)
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

  ||| The RIGHT side of an equality: in the ∈-less form a bare ⋆
  ||| parenthesizes — `… ≡ ⋆ using (…)` would otherwise reparse as
  ||| the ⋆-using proof form.
  eqSide : FixTable -> Maybe STy -> SElem -> Doc
  eqSide tbl Nothing (SStar _) = txt "(⋆)"
  eqSide tbl _ r = pe tbl LSumC False r

  eqSideT : FixTable -> Maybe STy -> SElem -> Doc
  eqSideT tbl Nothing (SStar _) = txt "(⋆)"
  eqSideT tbl _ r = pe tbl LOp0 False r

  ||| A written motive group, trailing space included; nothing when
  ||| elided.
  motDoc : FixTable -> Maybe (SName, STy) -> Doc
  motDoc tbl Nothing = DNil
  motDoc tbl (Just ((z, _), mot)) = txt " (\{z}. " <-> pt tbl TTop True mot <-> txt ")"

  classT : STy -> TCls
  classT ty = case ty of
    STyEq _ _ _ _ => CTTop
    STyPi _ _ _ => CTArrow
    STyImpPi _ _ _ => CTArrow
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
    STyEq _ l r mt =>
      pe tbl LOp0 False l <-> txt " ≡ " <-> eqSideT tbl mt r <->
      (case mt of
         Just t => txt " ∈ " <-> pt tbl TArrow True t
         Nothing => DNil)
    STyPi x a b =>
      if x == wildcard
        then pt tbl TSum False a <-> DGroup (DNest 2 (DLine <-> txt "→ " <-> pt tbl TTop True b))
        else tyPiRun tbl [(False, x, a)] b
    STyImpPi x a b => tyPiRun tbl [(True, x, a)] b
    STySigma x a b =>
      if x == wildcard
        then pt tbl TSum False a <-> DGroup (DNest 2 (DLine <-> txt "⨯ " <-> pt tbl TTop True b))
        else tySigmaRun tbl [(False, x, a)] b
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

-- ===== Comments =====
--
-- Comments never reach the AST (the lexer strips them), but their
-- ranges ride in mtokens and the source text in msrc, so the
-- distiller re-slices and RE-ATTACHES them: each comment goes to the
-- first body entry whose span it precedes or falls inside (an
-- intra-item comment hoists ABOVE its item — the rendered item has no
-- stable interior positions), comments before the first entry form
-- the file header (printed above the imports), and comments after
-- the last entry the epilogue. Attachment is idempotent: re-parsing
-- distilled output finds every comment immediately before its entry.

||| The module's comments, sliced from the retained source:
||| (start line, text). Only `--` line comments exist in practice; a
||| slice not comment-shaped (a block-comment continuation line) is
||| defensively prefixed.
unitComments : ModUnit -> List (Int, String)
unitComments u =
  let ls = lines u.msrc
  in sortBy (\a, b => compare (fst a) (fst b)) $
     mapMaybe (\(r, k) => case k of
                 Comment => Just (r.start.line, sliceAt ls r)
                 _ => Nothing) (toList u.mtokens)
 where
  asComment : String -> String
  asComment str = if isPrefixOf "--" str then str else "-- " ++ str

  sliceAt : List String -> Range -> String
  sliceAt ls r = case getAt (cast r.start.line) ls of
    Just l => asComment (pack (drop (cast r.start.column) (unpack l)))
    Nothing => "--"

entrySpan : SBodyEntry -> Maybe (Int, Int)
entrySpan (Left (mr, _)) = map (\r => (r.start.line, r.end.line)) mr
entrySpan (Right (mr, _)) = map (\r => (r.start.line, r.end.line)) mr

||| Render a whole module: header comments, imports, then the body in
||| source order with each comment re-attached before its entry.
export
renderUnit : ModUnit -> String
renderUnit u =
  let comments = unitComments u
      firstStart = head' (mapMaybe (map fst . entrySpan) u.mbody)
      (header, rest) = partition (\(l, _) => maybe True (\fs => l < fs) firstStart) comments
      imps = map renderImport u.mimports
      (blocks, leftover) = attach rest [] u.mbody
      headerBlock = case map snd header of
                      [] => []
                      hs => [joinBy "\n" hs]
      impBlock = case imps of
                   [] => []
                   _ => [joinBy "\n" imps]
      lastBlock = case map snd leftover of
                    [] => []
                    ls => [joinBy "\n" ls]
  in joinBy "\n\n" (headerBlock ++ impBlock ++ blocks ++ lastBlock) ++ "\n"
 where
  render1 : SBodyEntry -> String
  render1 (Left (_, f)) = renderFixity f
  render1 (Right (_, it)) = renderItemStr u.mfix it

  ||| Fold the body into BLOCKS, one per item, blank-line separated:
  ||| a comment glues to the entry it precedes (or sits inside), a
  ||| fixity line glues to the item that follows it.
  attach : List (Int, String) -> List String -> List SBodyEntry -> (List String, List (Int, String))
  attach cs pending [] = (case pending of [] => []; _ => [joinBy "\n" pending], cs)
  attach cs pending (e :: es) =
    let (mine, later) = case entrySpan e of
                          Just (_, end) => partition (\(l, _) => l <= end) cs
                          Nothing => ([], cs)
        pending' = pending ++ map snd mine ++ [render1 e]
    in case e of
         Left _ => attach later pending' es
         Right _ =>
           let (blocks, left) = attach later [] es
           in (joinBy "\n" pending' :: blocks, left)

-- ===== Sugar elision (Phase 4) =====
--
-- The distiller's emission of the ∈- and motive-elisions: sites whose
-- trial verdict is positive (the elided form provably recovers the
-- written annotation α-exactly) drop the annotation; everything else
-- stays written. Verdicts are keyed by (module, source range), so
-- already-elided files no-op (their sites record no verdicts).

parameters (ok : Range -> Bool, blankAt : Range -> Nat -> Bool)
  mutual
    esE : SElem -> SElem
    esE e = case e of
      SVar _ _ _ => e
      SSig _ _ => e
      SUnitI => e
      SZeroN => e
      SSuc t => SSuc (esE t)
      SLam x b => SLam x (esE b)
      SLet x d b => SLet x (esE d) (esE b)
      -- BLANK emission: on a Σ-headed spine, arguments at the trial's
      -- recorded item indices print as `_` (the whole set was
      -- verified as one joint recovery, so the emitted spine
      -- re-elaborates to the same core)
      SApp f a =>
        let (h, items) = surfSpine e [] in
        case h of
          SSig (Just rng) _ =>
            foldl SApp h (blankItems rng 0 items)
          _ => SApp (esE f) (esE a)
      SPair a b => SPair (esE a) (esE b)
      SProj1 t => SProj1 (esE t)
      SProj2 t => SProj2 (esE t)
      SZeroC => e
      SOneC => e
      SNatC => e
      SPiC x a b => SPiC x (esE a) (esE b)
      SSigmaC x a b => SSigmaC x (esE a) (esE b)
      SSumC a b => SSumC (esE a) (esE b)
      SQuotC a x y r => SQuotC (esE a) x y (esE r)
      SEqC rng l r t =>
        if maybe False ok rng
          then let (l', r') = elideSides l r in SEqC rng l' r' Nothing
          else SEqC rng (esE l) (esE r) (map esT t)
      SZeroElim t => SZeroElim (esE t)
      SNatElim mot z n2 ih st t =>
        SNatElim (esMot mot) (esE z) n2 ih (esE st) (esE t)
      SInj1 t => SInj1 (esE t)
      SInj2 t => SInj2 (esE t)
      SSumElim mot a l b r t =>
        SSumElim (esMot mot) a (esE l) b (esE r) (esE t)
      SClass t => SClass (esE t)
      SQuotElim mot a f q => SQuotElim (esMot mot) a (esE f) (esE q)
      SNuC f => SNuC (esP f)
      SOut t => SOut (esE t)
      SCorec x a f u => SCorec x (esE a) (esE f) (esE u)
      SCoind nx ny r pw mx my mh w => SCoind nx ny (esE r) (esE pw) mx my mh (esE w)
      SSquash t => SSquash (esT t)
      SStar _ => e
      SStarWit w => SStarWit (esE w)
      SStarUsing _ _ => e
      SSquashElim sc x b => SSquashElim (esE sc) x (esE b)
      SChain h links => SChain (esE h) (map (\(j, m) => (esE j, esE m)) links)
      SAnn t ty => SAnn (esE t) (esT ty)
      SImpArg t => SImpArg (esE t)
      SNoIns t => SNoIns (esE t)
      SBlank _ => e

    surfSpine : SElem -> List SElem -> (SElem, List SElem)
    surfSpine (SApp f a) acc = surfSpine f (a :: acc)
    surfSpine h acc = (h, acc)

    blankItems : Range -> Nat -> List SElem -> List SElem
    blankItems rng i [] = []
    blankItems rng i (it :: rest) =
      (if blankAt rng i then SBlank Nothing else esE it) :: blankItems rng (S i) rest

    ||| An ∈-elided equality INFERS one side (left first — mirror
    ||| elabEqSides); that side's ROOT motive must stay written even
    ||| when its own verdict allows elision, or the side stops being
    ||| inferable — the one cross-sugar interaction.
    elideSides : SElem -> SElem -> (SElem, SElem)
    elideSides l r =
      if sInferForm l
        then (keepRootMotive l, esE r)
        else (esE l, keepRootMotive r)

    keepRootMotive : SElem -> SElem
    keepRootMotive e = case e of
      SNatElim (Just (n, m)) z n2 ih st t =>
        SNatElim (Just (n, esT m)) (esE z) n2 ih (esE st) (esE t)
      SSumElim (Just (z, m)) a lb b rb t =>
        SSumElim (Just (z, esT m)) a (esE lb) b (esE rb) (esE t)
      SQuotElim (Just (z, m)) a f q =>
        SQuotElim (Just (z, esT m)) a (esE f) (esE q)
      _ => esE e

    esMot : Maybe (SName, STy) -> Maybe (SName, STy)
    esMot Nothing = Nothing
    esMot (Just ((z, mr), mot)) =
      if maybe False ok mr then Nothing else Just ((z, mr), esT mot)

    esT : STy -> STy
    esT ty = case ty of
      STyPi x a b => STyPi x (esT a) (esT b)
      STyImpPi x a b => STyImpPi x (esT a) (esT b)
      STySigma x a b => STySigma x (esT a) (esT b)
      STySum a b => STySum (esT a) (esT b)
      STyQuot a x y r => STyQuot (esT a) x y (esE r)
      STyEq rng l r t =>
        if maybe False ok rng
          then let (l', r') = elideSides l r in STyEq rng l' r' Nothing
          else STyEq rng (esE l) (esE r) (map esT t)
      STyEl t => STyEl (esE t)
      STyPrf t => STyPrf (esE t)
      STyNu f => STyNu (esP f)
      _ => ty

    esP : SPoly -> SPoly
    esP pl = case pl of
      SPHole => pl
      SPConst a => SPConst (esE a)
      SPProd f g => SPProd (esP f) (esP g)
      SPSum f g => SPSum (esP f) (esP g)
      SPSigma x a f => SPSigma x (esE a) (esP f)
      SPPi x a f => SPPi x (esE a) (esP f)

  esQDecl : SQDecl -> SQDecl
  esQDecl (MkSQDecl n bs res) =
    MkSQDecl n (map (\(x, d) => (x, case d of
                                     Left t => Left (esT t)
                                     Right qt => Right (esQTm qt))) bs)
      (case res of
         SQResU => SQResU
         SQResEl t => SQResEl (esQTm t)
         SQResEq l r u => SQResEq (esQTm l) (esQTm r) (esQTm u))
   where
    esQTm : SQTm -> SQTm
    esQTm (SQVar n i) = SQVar n i
    esQTm (SQAppE f e) = SQAppE (esQTm f) (esE e)
    esQTm (SQAppI f a) = SQAppI (esQTm f) (esQTm a)

  esItem : SItem -> SItem
  esItem (SDef x ty body mu) = SDef x (esT ty) (esE body) mu
  esItem (SDeclDef r x ty) = SDeclDef r x (esT ty)
  esItem (STypeDef x ty) = STypeDef x (esT ty)
  esItem (SData params ds) = SData (map (\(x, t) => (x, esT t)) params) (map esQDecl ds)
  esItem (SClausalDef r x ty eta wit cls) =
    SClausalDef r x (esT ty) eta (map esE wit) (map ({ crhs $= esE }) cls)

||| Apply the verdict map to one module.
elideSugar : List (String, Range, Bool) -> List (String, Range, Nat) -> ModUnit -> ModUnit
elideSugar verdicts blanks u =
  let ok = \r => any (\(m, r', v) => v && m == u.mname && show r' == show r) verdicts
      blankAt = \r, i => any (\(m, r', j) => m == u.mname && j == i && show r' == show r) blanks
      body' = map (map (\(r, it) => (r, esItem ok blankAt it))) u.mbody
  in { mbody := body', mitems := mapMaybe (\e => case e of
                                             Right ri => Just ri
                                             Left _ => Nothing) body' } u

||| Entrywise α-comparison of two kernel Σs (core is nameless, so
||| structural equality is α-equality; Show on components is the
||| comparator).
export
sigCompare : Sig -> Sig -> Maybe String
sigCompare a b = go (toList a) (toList b)
 where
  showEntry : SigEntry -> String
  showEntry (SigDef ctx n body ty) = "def \{n} : \{show ty} ≔ \{show body} [\{show ctx}]"
  showEntry (SigTyDef ctx n ty) = "type \{n} ≔ \{show ty} [\{show ctx}]"
  showEntry (SigDecl ctx n ty) = "decl \{n} : \{show ty} [\{show ctx}]"
  showEntry (SigTyDecl ctx n) = "tydecl \{n} [\{show ctx}]"
  showEntry (SigEq ctx l r ty) = "eq \{show l} ≐ \{show r} : \{show ty} [\{show ctx}]"
  showEntry (SigTyEq ctx x y) = "tyeq \{show x} ≐ \{show y} [\{show ctx}]"

  go : List SigEntry -> List SigEntry -> Maybe String
  go [] [] = Nothing
  go (x :: xs) (y :: ys) =
    if showEntry x == showEntry y then go xs ys
    else Just ("Σ entry differs after distill:\n  original: \{showEntry x}\n  new:      \{showEntry y}")
  go _ _ = Just "Σ length differs after distill"

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
  else if map (fixShow . snd) (lefts orig.mbody) /= map (fixShow . snd) (lefts re.mbody)
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

export
verifyUnits : List ModUnit -> List ModUnit -> Maybe String
verifyUnits [] [] = Nothing
verifyUnits (u :: us) (v :: vs) =
  case verifyUnit u v of
    Just err => Just err
    Nothing => verifyUnits us vs
verifyUnits us vs = Just "module count differs after distill (\{show (length us)} vs \{show (length vs)})"

-- ===== IO driver =====

export
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

export
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
||| Iterate blank emission to its fixpoint: re-run the sugar-trial
||| elaboration on the emitted modules and apply any newly verdicted
||| elisions, until a round adds nothing (fuel-capped; the set is
||| monotone, so the cap is a formality).
blankFix : Nat -> List ModUnit -> Nat -> (List ModUnit, Nat)
blankFix Z us n = (us, n)
blankFix (S fuel) us n =
  case elabProgramSugar us of
    Left _ => (us, n)
    Right (_, vs, bs) =>
      let fresh = filter (\(_, _, v) => v) vs in
      if null bs && null fresh
        then (us, n)
        else blankFix fuel (map (elideSugar vs bs) us) (n + length bs)

||| then verify the round trip — re-parsed ASTs structurally identical,
||| re-elaboration output identical (docs/NovaPerfectSurface.txt,
||| "Phase 1, precisely").
export
distillPath : (rootPath : String) -> (outDir : String) -> IO (Either String String)
distillPath rootPath outDir = do
  Right units <- loadProgram rootPath
    | Left err => pure (Left err.lmsg)
  -- the acceptance run doubles as the SUGAR TRIAL: per written
  -- ∈-annotation and motive, would the elided form recover it
  -- α-exactly? (docs/NovaPerfectSurface.txt, Phase 4)
  let Right (sigOrig, verdicts, blanks) = elabProgramSugar units
    | Left err => pure (Left ("input is not accepted; distill only transforms accepted programs:\n" ++ err))
  let False = normDir (dirOf rootPath) == normDir outDir
    | True => pure (Left "output directory equals the source directory; refusing to overwrite sources")
  -- blank emission iterates to a FIXPOINT: blanking an argument
  -- flips the spines inside it from checking to inference at the
  -- next elaboration, and inference-mode verdicts can unlock
  -- positions the checked-mode pass could not verify (the verdict
  -- demands recovery in every mode the site might face, and a flip
  -- removes the checked mode from that set). The blank set only
  -- grows — holes are only added, and mode flips only go
  -- checked → inferred — so the iteration converges; each round's
  -- emission is re-verdicted by a full sugar-trial elaboration, and
  -- the final corpus is Σ-gated against the ORIGINAL below.
  let (elided, nBlanks) = blankFix 16 (map (elideSugar verdicts blanks) units) (length blanks)
  Right () <- writeUnits outDir (baseName rootPath) elided
    | Left err => pure (Left err)
  Right units' <- loadProgram (outDir ++ "/" ++ baseName rootPath)
    | Left err => pure (Left ("distilled output failed to load: " ++ err.lmsg))
  let Nothing = verifyUnits elided units'
    | Just err => pure (Left err)
  () <- clearSigEntryIx
  let Right sigNew = elabProgramSig units'
    | Left err => pure (Left ("distilled output failed to elaborate:\n" ++ err))
  let Nothing = sigCompare sigOrig sigNew
    | Just err => pure (Left err)
  let nElided = length (filter (\(_, _, v) => v) verdicts)
  pure (Right ("distilled \{show (length units)} modules (\{show (countItems units)} items) to \{outDir}\n" ++
               "elided \{show nElided} of \{show (length verdicts)} ∈-annotations and motives, blanked \{show nBlanks} arguments\n" ++
               "round-trip OK: ASTs identical, kernel Σ α-identical."))
