module Nova.Eliminate

-- IN-PLACE ELIMINATION (docs/NovaElaboration.txt, In-place
-- elimination): given a HOLE and a VARIABLE of its context, the
-- surface text that replaces the hole's own span, with one new hole
-- per goal that remains.
--
-- Nothing here elaborates. It READS a finished run's hole view — the
-- context, the goal and the `?x` span that `mintHole` recorded — and
-- WRITES text for the next run to elaborate. It emits through the
-- REPORT's own printer, so the motive this module writes and the goal
-- the operator reads are one rendering.
--
-- Two tiers, decided by whether the refined goal is CONVERTIBLE to the
-- original (the spec's table): a POSITIVE former gets its eliminator
-- and a hole per branch, and abstracts the dependency-closed suffix; a
-- RETYPE former (×, 𝟙, ≡) gets an ascribed hole and abstracts nothing.

import Data.List
import Data.List1
import Data.Maybe
import Data.SnocList
import Data.String

import Me.Russoul.Text.Position
import Me.Russoul.Text.Range

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel.Parser
import Nova.Elaboration.Surface
import Nova.Recovery
import Nova.Elaboration.Named
import Nova.Elaboration
import Nova.Elaboration.Loader

import System.File

%default covering

-- ===== options =====

||| Everything the caller may choose. Each form has an ordered list of
||| NAME SLOTS and of new-hole LABELS (docs/NovaElaboration.txt,
||| Names); a caller supplies a PREFIX of either, and every unsupplied
||| slot takes its default. An empty string means "default" too, so a
||| later slot can be set without naming the earlier ones.
public export
record Options where
  constructor MkOptions
  optNames  : List String
  optLabels : List String
  ||| a Σ split iterates to the LEAVES instead of stopping one down
  optDeep   : Bool

export
defaultOptions : Options
defaultOptions = MkOptions [] [] False

-- ===== small list/name helpers =====

at : Nat -> List a -> Maybe a
at _     []        = Nothing
at Z     (x :: _)  = Just x
at (S k) (_ :: xs) = at k xs

nameOr : List String -> Nat -> String
nameOr nms p = fromMaybe "_" (at p nms)

toSnoc : List a -> SnocList a
toSnoc = foldl (:<) [<]

||| Position of the first occurrence, if any.
indexOf : Eq a => a -> List a -> Maybe Nat
indexOf x xs = go 0 xs
 where
  go : Nat -> List a -> Maybe Nat
  go _ [] = Nothing
  go i (y :: ys) = if y == x then Just i else go (S i) ys

||| Slot i of an override list, "" and absent alike meaning default.
pick : List String -> Nat -> (dflt : String) -> String
pick xs i dflt = case at i xs of
  Just x  => if x == "" then dflt else x
  Nothing => dflt

||| A label no other hole of the item already carries (e-hole: a second
||| `?a` in one item is a structural error).
freshLabel : (taken : List String) -> String -> String
freshLabel taken base = if base `elem` taken then go 1 else base
 where
  go : Nat -> String
  go k = let c = base ++ show k in if c `elem` taken then go (S k) else c

||| The operator's label, without the `?` the report prints it with.
bareLabel : String -> String
bareLabel x = pack (drop 1 (unpack (holeLabel x)))

||| The ITEM a hole's Σ name belongs to: everything before the LAST
||| dot (`?dbl.step` is dbl's). Two holes may share a label only when
||| they belong to different items.
holeItem : String -> String
holeItem x = pack (reverse (drop 1 (dropWhile (/= '.') (reverse (unpack x)))))

||| An argument-position spelling: a printed term that is not already
||| one token stands parenthesized. Over-parenthesizing is harmless;
||| under-parenthesizing would re-associate the splice.
atomize : String -> String
atomize s = if any isSpace (unpack s) then "(" ++ s ++ ")" else s

||| Continuation lines indent to the hole's own column.
indentAt : (col : Int) -> (extra : Nat) -> String
indentAt col extra =
  pack (replicate (integerToNat (cast (max 0 col)) + extra) ' ')

||| Re-applying a Π-closed eliminator to the entries it closed makes
||| an APPLICATION, and a hole is an ATOM — so the whole thing takes
||| one more pair of parentheses, or a hole in an argument position
||| would re-associate (docs/NovaElaboration.txt, Splicing).
closeApp : (apps : String) -> String -> String
closeApp "" body = body
closeApp apps body = "(" ++ body ++ apps ++ ")"

||| A multi-line replacement, opened by its own paren and continued
||| under it: a hole is an ATOM, so what replaces it must be one.
parenLines : (col : Int) -> List String -> String
parenLines col []          = ""
parenLines col (l :: rest) =
  joinBy "\n" (("(" ++ l) :: map (indentAt col 1 ++) rest)

-- ===== the context, by POSITION =====
--
-- Positions run OUTERMOST-first (0 = outermost), de Bruijn indices
-- innermost-first, so position p of a length-n context is index
-- n-1-p, and a term standing at position p refers to position q by
-- index p-1-q.

posOfIndex : (len : Nat) -> Nat -> Nat
posOfIndex n k = minus (minus n 1) k

idxOfPos : (p, q : Nat) -> Nat
idxOfPos p q = minus (minus p 1) q

mentionsAt : List Ty -> (p, q : Nat) -> Bool
mentionsAt tys p q = case at p tys of
  Just t  => usesIndexTy (idxOfPos p q) t
  Nothing => False

||| Positions a term standing at p mentions (p == n reads a term over
||| the WHOLE context, i.e. the goal).
mentionedBy : (t : Ty) -> (p : Nat) -> List Nat
mentionedBy t p = filter (\q => usesIndexTy (idxOfPos p q) t) [0 .. minus p 1]

||| THE DEPENDENCY-CLOSED SUFFIX: positions after px whose type
||| mentions px, or an entry already in the closure. Ascending, order
||| preserved; everything outside stays where it is.
closure : List Ty -> (px : Nat) -> List Nat
closure tys px = go (S px) [px] []
 where
  go : Nat -> List Nat -> List Nat -> List Nat
  go p seen acc =
    if p >= length tys
      then reverse acc
      else if any (mentionsAt tys p) seen
             then go (S p) (p :: seen) (p :: acc)
             else go (S p) seen acc

-- ===== what a variable's type exposes =====

data Former
  = FNat
  | FSum
  | FZero
  | FQuot
  | FSquash
  | FSigma
  | FUnit
  | ||| an equation, with its two sides
    FEq Elem Elem

former : Ty -> Maybe Former
former Elem.NatTy         = Just FNat
former (Elem.SumTy _ _)   = Just FSum
former Elem.ZeroTy        = Just FZero
former (QuotTy _ _)       = Just FQuot
former (Squash _)         = Just FSquash
former (Elem.SigmaTy _ _) = Just FSigma
former Elem.OneTy         = Just FUnit
former (Elem.EqTy l r _)  = Just (FEq l r)
former _                  = Nothing

-- ===== restating a goal =====

||| The goal, restated with position p spelled as `txt`. The
||| replacement need not be a NAME, so it is spliced into the printing
||| environment at p — sound because every slot this module fills is a
||| delimited group or an atom (docs/NovaElaboration.txt, Splicing).
restate : FixTable -> (nms : List String) -> (n, p : Nat)
       -> (txt : String) -> Ty -> String
restate tbl nms n p txt goal =
  let env = toSnoc (map (\q => if q == p then txt else nameOr nms q) [0 .. minus n 1])
  in prettyTyN tbl env goal

-- ===== the Σ split =====

||| One component a Σ split names: its name, whether it BINDS (a 𝟙
||| component contributes () and binds nothing), which projection it
||| is, and the PARENT it projects from — Nothing for the eliminated
||| variable itself, `Just j` for the j-th component of this same
||| split. Parents come before children (depth-first), so every let is
||| a ONE-STEP projection off a name already bound.
record Comp where
  constructor MkComp
  cName   : String
  cBind   : Bool
  cFirst  : Bool
  cParent : Maybe Nat
  cBase   : String

||| The components a Σ variable splits into: one step down, or all the
||| way to the leaves. `pe` is the parent as a term of the AMBIENT
||| context (what the second component's type is instantiated at);
||| `start` is the index the first emitted component takes, and its
||| NAME SLOT.
splitComps : (names : List String) -> (deep : Bool) -> (pe : Elem)
          -> (base : String) -> (parent : Maybe Nat) -> Ty
          -> (start, depth : Nat) -> List Comp
splitComps names deep pe base parent ty start depth = case (ty, depth < 8) of
  (Elem.SigmaTy a b, True) =>
    let b' : Ty
        b' = substTy b (Ext Id (SigmaElim1 pe))
        c1 : Comp
        c1 = comp a (base ++ "1") True start
        sub1 : List Comp
        sub1 = if deep
                 then splitComps names deep (SigmaElim1 pe) c1.cName (Just start) a (S start) (S depth)
                 else []
        i2 : Nat
        i2 = S start + length sub1
        c2 : Comp
        c2 = comp b' (base ++ "2") False i2
        sub2 : List Comp
        sub2 = if deep
                 then splitComps names deep (SigmaElim2 pe) c2.cName (Just i2) b' (S i2) (S depth)
                 else []
    in (c1 :: sub1) ++ (c2 :: sub2)
  _ => []
 where
  comp : Ty -> (dflt : String) -> (first : Bool) -> (slot : Nat) -> Comp
  comp cty dflt first slot = case cty of
    Elem.OneTy => MkComp "()" False first parent base
    _          => MkComp (pick names slot dflt) True first parent base

||| What a whole-variable occurrence is restated AT: the tuple its
||| components form, built from the components themselves so that a
||| renamed one is spelled the way its let binds it.
tupleFrom : List Comp -> (parent : Maybe Nat) -> (fallback : String) -> String
tupleFrom comps parent fallback =
  case [ (i, c) | (i, c) <- zip [0 .. length comps] comps, c.cParent == parent ] of
    [(i1, c1), (i2, c2)] =>
      "(\{tupleFrom comps (Just i1) c1.cName}, \{tupleFrom comps (Just i2) c2.cName})"
    _ => fallback

||| The goal a Σ split restates, read at the COMPONENTS: every
||| occurrence of a component's projection becomes that component's
||| name (scrutinee abstraction again — `absT`, the motive-recovery
||| primitive), and any occurrence of the variable ITSELF becomes the
||| tuple. Without the abstraction step the goal would read
||| `P ((x1, x2) .π₁)` where the operator wants `P x1`.
restateSplit : FixTable -> (nms : List String) -> (n, px, k : Nat)
            -> List Comp -> (tup : String) -> Ty -> String
restateSplit tbl nms n px k comps tup goal =
  let abstracted : Ty
      abstracted = snd (foldl step (0, goal) comps)
      env : NameEnv
      env = toSnoc (map (\q => if q == px then tup else nameOr nms q) [0 .. minus n 1]
                      ++ map cName comps)
  in prettyTyN tbl env abstracted
 where
  ||| The parent, as a term of the context i abstractions have already
  ||| extended: the eliminated variable has shifted by i, and the j-th
  ||| component sits at index i-1-j.
  step : (Nat, Ty) -> Comp -> (Nat, Ty)
  step (i, g) c =
    let pe : Elem
        pe = case c.cParent of
               Nothing => CtxVar (k + i)
               Just j  => CtxVar (minus (minus i 1) j)
        t : Elem
        t = if c.cFirst then SigmaElim1 pe else SigmaElim2 pe
    in (S i, absT 0 t g)

-- ===== the generalized suffix's own conditions =====

||| Evidently a proposition, by its former alone — enough to know that
||| ⋆ stands for it (el-prf-prop: proofs are irrelevant, so ANY
||| inhabitant does, and the ambient one is in scope to discharge it).
evidentProp : Ty -> Bool
evidentProp (Elem.EqTy _ _ _) = True
evidentProp (Squash _)        = True
evidentProp _                 = False

||| An ANONYMOUS entry has no spelling: `_` resolves to nothing (Name
||| resolution), so it can be neither re-applied nor mentioned. A
||| PROPOSITION needs no spelling — ⋆ stands for it — which is exactly
||| what makes a let's own unfolding equation generalizable, and the
||| convoy the closure rule subsumes work. Anything else is refused
||| rather than emitted as a blank.
anonCheck : (tys : List Ty) -> (nms : List String) -> (gen : List Nat)
         -> (n : Nat) -> (goal : Ty) -> Maybe String
anonCheck tys nms gen n goal =
  let mentioned = nub (mentionedBy goal n
                        ++ concatMap (\p => maybe [] (\t => mentionedBy t p) (at p tys)) gen)
      anons = filter (\p => nameOr nms p == wildcard) gen in
  case filter (\p => p `elem` mentioned) anons of
    (p :: _) => Just "an anonymous entry of the context must be generalized here, and the goal mentions it — a blank has no spelling, so name that binder first"
    [] => case filter (\p => not (maybe False evidentProp (at p tys))) anons of
            (p :: _) => Just "an anonymous entry of the context must be generalized here, and it is not a proposition — a blank has no spelling, so name that binder first"
            [] => Nothing

-- ===== capture =====

||| A generated binder may SHADOW only names the emitted text does not
||| mention: the printing environment places NAMES, so a binder
||| capturing an occurrence would change what that occurrence means.
||| The defaults always pass — what they shadow is the eliminated
||| variable, which the emitted text no longer mentions.
captureCheck : (tys : List Ty) -> (nms, renamed : List String)
            -> (gen : List Nat) -> (px, n : Nat) -> (goal : Ty) -> Maybe String
captureCheck tys nms renamed gen px n goal =
  let bound = map (nameOr renamed) (px :: gen)
      free  = nub (mentionedBy goal n
                     ++ concatMap (\p => maybe [] (\t => mentionedBy t p) (at p tys)) gen)
      loose = filter (\q => q /= px && not (q `elem` gen)) free
      clash = filter (\q => nameOr nms q `elem` bound) loose
  in case clash of
       []       => Nothing
       (q :: _) => Just "a generated binder would capture \{nameOr nms q}, which this goal mentions — name it something else"

-- ===== the generated QIIT eliminator =====

||| The head of a signature-reference spine, with its arguments: how a
||| QIIT sort presents once the report has folded the carried former
||| back through the def that NAMES it (`resugarQ`) — `Bag ℕ`, not
||| 𝒮{U; …}.0[].
spineHead : Elem -> Maybe (String, List Elem)
spineHead (SigVar x _) = Just (x, [])
spineHead (PiApp f a) = map (\hd => (fst hd, snd hd ++ [a])) (spineHead f)
spineHead _ = Nothing

||| The METHOD binders of a point constructor, in the ᴰ-walk's order:
||| each argument, and immediately after an inductive one its induction
||| hypothesis. Defaults are the constructor's OWN binder names, which
||| the `data` item wrote; the induction hypothesis is `ih` where there
||| is one to name, and `ih<arg>` where there are several.
methodBinders : (names : List String) -> (offset : Nat) -> QIITCtor
             -> (List String, Nat)
methodBinders names offset c =
  let inds = length (filter qaInductive c.qcArgs)
  in go inds offset 1 c.qcArgs
 where
  -- a `data` item may leave a constructor's argument ANONYMOUS
  -- (`s : El N → El N`), and `_` resolves to nothing — so a method
  -- binder that would be blank is named by its position instead,
  -- which is what makes the branch able to use it
  go : Nat -> Nat -> Nat -> List QIITArg -> (List String, Nat)
  go _ o _ [] = ([], o)
  go inds o i (a :: rest) =
    let dflt = if a.qaName == wildcard then "a" ++ show i else a.qaName
        nm = pick names o dflt in
    if a.qaInductive
      then let ih = pick names (S o) (if inds == 1 then "ih" else "ih" ++ nm)
               (more, o') = go inds (S (S o)) (S i) rest
           in (nm :: ih :: more, o')
      else let (more, o') = go inds (S o) (S i) rest
           in (nm :: more, o')

||| A λ-chain over the given binders, ending in `body`; a chain with no
||| binders is the body itself.
lamChain : List String -> (body : String) -> String
lamChain [] body = body
lamChain bs body = "(" ++ concat (map (\b => "λ\{b}. ") bs) ++ body ++ ")"

||| One argument group per line when the whole application does not
||| fit; `parenLines` opens the paren, so the last group closes it.
layoutApp : (col : Int) -> (head : String) -> List String -> String
layoutApp col hd args =
  let flat = hd ++ concat (map (" " ++) args) in
  if length flat + integerToNat (cast (max 0 col)) <= 76
    then "(" ++ flat ++ ")"
    else case args of
           [] => "(" ++ hd ++ ")"
           -- the head keeps its FIRST argument (a motive, or the
           -- parameters an eliminator lemma leads with), as the
           -- eliminator forms do
           (a0 :: rest) => case reverse rest of
             [] => "(" ++ hd ++ " " ++ a0 ++ ")"
             (lastA :: revInit) =>
               parenLines col ((hd ++ " " ++ a0) :: reverse revInit ++ [lastA ++ ")"])

-- ===== the emitter =====

||| Text that replaces the hole's span, with the span itself. The
||| caller splices it (`spliceAt`) and re-elaborates: this module never
||| decides that what it wrote is right.
||| CANDIDATES, in preference order: the caller takes the first that
||| verifies (`eliminateEdit`). Two forms differ only in what the
||| elaborator is asked to recover — a motive it can read off the
||| expected type, or the flavor of eliminator a goal's universe wants
||| — and trying the preferred one first, with the other behind it,
||| keeps that judgement out of this module and in the trial.
export
eliminate : Options -> (taken : List String) -> (qiits : List QIITInfo)
         -> HoleView -> (var : String) -> Either String (List (Range, String))
eliminate opts taken qiits v var =
  case (h.dvrange, h.dvty) of
    (Nothing, _) => Left "the hole has no source span to replace"
    (_, Nothing) => Left "a TYPE hole has no goal to eliminate into"
    (Just rng, Just goal) =>
      let tys = toList h.dvctx
          nms = toList h.dvenv
          n   = length tys in
      case resolveName h.dvenv var of
        Nothing => Left "\{var} is not a variable of this goal's context"
        Just k => case at (posOfIndex n k) tys of
          Nothing => Left "\{var} is not a variable of this goal's context"
          Just vty =>
            let px      = posOfIndex n k
                -- the same entry, head EXPOSED: what the former is
                -- read off, since the display form keeps a definition
                -- folded (`bisim s t`, whose former is a squash)
                vtyX    = fromMaybe vty (at (posOfIndex n k) tysX)
                label   = bareLabel h.dvname
                col     = rng.start.column
                gen     = closure tys px
                -- printing names: each slot keeps its own name unless
                -- the caller renamed a generalized entry's binder. The
                -- eliminated variable's slot takes the motive binder,
                -- which is its own name — what it shadows is exactly
                -- the variable being eliminated
                renamed = map (\p => if p == px then var
                                       else case indexOf p gen of
                                              Just i  => pick opts.optNames (2 + i) (nameOr nms p)
                                              Nothing => nameOr nms p)
                              [0 .. minus n 1]
                pfx     = \p => toSnoc (take p renamed)
                tele    = concat (map (\p => case at p tys of
                                               Just t  => "(\{nameOr renamed p} : \{prettyTyN tbl (pfx p) t}) → "
                                               Nothing => "")
                                      gen)
                motive  = "\{var}. " ++ tele ++ prettyTyN tbl (pfx n) goal
                lams    = concat (map (\p => "λ\{nameOr renamed p}. ") gen)
                -- an anonymous entry is re-applied as ⋆: it is a
                -- proposition (anonCheck), so proof irrelevance makes
                -- any inhabitant do and the ambient one discharges it
                apps    = concat (map (\p => if nameOr nms p == wildcard
                                              then " ⋆"
                                              else " " ++ nameOr nms p) gen)
                -- a motive the elaborator RECOVERS need not be
                -- written: it abstracts the scrutinee in the expected
                -- type, which is what this closure is when it closes
                -- nothing. Skeleton-freedom is the recovery's own
                -- precondition
                bare    = null gen && skelFreeT (absT 0 (CtxVar k) goal)
                lbl     = \i, tag => freshLabel taken (pick opts.optLabels i (label ++ tag))
                own     = freshLabel taken label
            in case ( former vtyX
                    , captureCheck tys nms renamed gen px n goal
                        <|> anonCheck tys nms gen n goal ) of
                 (_, Just err) => Left err
                 (Nothing, _) => case qiitAt qiits vty of
                   -- a QIIT SORT: no expression-level eliminator
                   -- exists, so eliminating a variable of one is
                   -- APPLYING the pair of lemmas its data item
                   -- generated (docs/NovaElaboration.txt)
                   Just (info, args) =>
                     qiitElim info args rng goal nms n px col var motive lams apps own label
                   Nothing => byEquation tbl opts taken h var rng goal tys nms n px own
                 (Just FZero, _) => Right [(rng, "(𝟘-elim \{var})")]
                 (Just FSquash, _) =>
                   Right [(rng, "(squash-elim \{var} (\{pick opts.optNames 0 var}. ?\{lbl 0 "Sq"}))")]
                 (Just FNat, _) =>
                   let p = pick opts.optNames 0 var
                       i = pick opts.optNames 1 "ih" in
                   Right (candidates rng bare
                     "(ℕ-elim ?\{lbl 0 "Z"} (\{p} \{i}. ?\{lbl 1 "S"}) \{var})"
                     (closeApp apps $ parenLines col
                            -- the z slot is an ATOM position
                            -- (parseSElemAtom), unlike the delimited
                            -- case groups: a λ-closed branch needs its
                            -- own parens
                            [ "ℕ-elim (\{motive})"
                            , "(\{lams}?\{lbl 0 "Z"})"
                            , "(\{p} \{i}. \{lams}?\{lbl 1 "S"})"
                            , "\{var})" ]))
                 (Just FSum, _) =>
                   let l = pick opts.optNames 0 var
                       r = pick opts.optNames 1 var in
                   Right (candidates rng bare
                     "(⊎-elim (\{l}. ?\{lbl 0 "Inl"}) (\{r}. ?\{lbl 1 "Inr"}) \{var})"
                     (closeApp apps $ parenLines col
                            [ "⊎-elim (\{motive})"
                            , "(\{l}. \{lams}?\{lbl 0 "Inl"})"
                            , "(\{r}. \{lams}?\{lbl 1 "Inr"})"
                            , "\{var})" ]))
                 (Just FQuot, _) =>
                   let a = pick opts.optNames 0 var in
                   Right (candidates rng bare
                     "(quot-elim (\{a}. ?\{lbl 0 "Cls"}) \{var})"
                     (closeApp apps $ parenLines col
                            [ "quot-elim (\{motive})"
                            , "(\{a}. \{lams}?\{lbl 0 "Cls"})"
                            , "\{var})" ]))
                 -- RETYPE: the refined goal IS the original
                 -- judgementally, so nothing is abstracted and no
                 -- branch is opened — the artifact is an ascribed
                 -- hole, and for × the lets that name what it is
                 -- stated at
                 (Just FUnit, _) =>
                   if not (usesIndexTy k goal)
                     then Left "the goal does not mention \{var}, so eliminating it refines nothing"
                     else Right [(rng, "(?\{own} : \{restate tbl nms n px "()" goal})")]
                 (Just FSigma, _) =>
                   let comps = splitComps opts.optNames opts.optDeep (CtxVar k) var Nothing vty 0 0
                       tup   = tupleFrom comps Nothing var
                       bound = map cName (filter cBind comps)
                       seen  = map (nameOr nms) (filter (/= px) (mentionedBy goal n))
                       body  = if usesIndexTy k goal
                                 then "(?\{own} : \{restateSplit tbl nms n px k comps tup goal})"
                                 else "?\{own}"
                       txt   = concat (map (\c => "let \{c.cName} ≔ \{c.cBase} \{if c.cFirst then ".π₁" else ".π₂"} in\n" ++ indentAt col 1)
                                           (filter cBind comps))
                   in case filter (\b => b `elem` seen) bound of
                        (b :: _) => Left "a component named \{b} would capture the \{b} this goal already mentions — name it something else"
                        [] => Right [(rng, "(" ++ txt ++ body ++ ")")]
                 (Just (FEq l r), _) =>
                   -- the named thing IS an equation: rewrite its
                   -- VARIABLE side to the other one. Its sides are
                   -- indexed from the equation's OWN position, and
                   -- print in the scope that ends there
                   let scope : NameEnv
                       scope = toSnoc (take px (map (nameOr nms) [0 .. minus n 1])) in
                   case (l, r) of
                     (CtxVar i, _) => retype tbl nms n (idxOfPos px i) goal own
                                        (prettyElemN tbl scope r)
                     (_, CtxVar i) => retype tbl nms n (idxOfPos px i) goal own
                                        (prettyElemN tbl scope l)
                     _ => Left "\{var} : neither side of this equation is a variable"
 where
  tbl : FixTable
  tbl = v.hvFix

  h : DeclView
  h = v.hvDecl

  ||| CLASSIFY on the exposed context, PRINT from the display one: a
  ||| type is usually written as a definition, and its former shows
  ||| only after exposure.
  tysX : List Ty
  tysX = toList v.hvCtxX

  ||| A QIIT sort, recognized through the def that NAMES it, with the
  ||| arguments it stands at.
  qiitAt : List QIITInfo -> Ty -> Maybe (QIITInfo, List Elem)
  qiitAt infos ty = do
    (hd, args) <- spineHead ty
    info <- find (\i => i.qiSort == hd) infos
    pure (info, args)

  ||| Applying the generated eliminator: parameters, one motive per
  ||| SORT of the signature, one η-expanded method per point
  ||| constructor, one coherence per equation constructor (the
  ||| code-valued flavor only), then the eliminee.
  |||
  ||| Both flavors are offered, the evident one first: a goal that is
  ||| a proposition by its former alone wants the Ω-valued eliminator,
  ||| anything else the 𝕌-valued one — and the trial settles the cases
  ||| a former cannot (a prop-valued neutral goal).
  qiitElim : QIITInfo -> (args : List Elem) -> Range -> Ty
          -> (nms : List String) -> (n, px : Nat) -> (col : Int)
          -> (var, motive, lams, apps, own, label : String)
          -> Either String (List (Range, String))
  qiitElim info args rng goal nms n px col var motive lams apps own label =
    if info.qiIndices /= 0
      then Left "\{var} : \{info.qiSort} is an INDEXED sort, whose motive must abstract its indices too — not yet emitted"
    else if length args /= info.qiParams
      then Left "\{var} : \{info.qiSort} stands at \{show (length args)} arguments, and its data item declares \{show info.qiParams} parameters"
    else
      let -- the sort's arguments live in the context PREFIX that ends
          -- at the variable, so they print under that prefix's names,
          -- not the whole context's
          env : NameEnv
          env = toSnoc (take px (map (nameOr nms) [0 .. minus n 1]))
          ps : List String
          ps = map (atomize . prettyElemN tbl env) args
          -- the eliminated sort's motive is the goal, abstracted by
          -- the SHADOWING the variable's own name already does; every
          -- other sort's is a hole at its own declared domain
          mots : List String
          mots = map (\im => if fst im == info.qiPos
                               then "(λ\{var}. \{motive'})"
                               else "?" ++ freshLabel taken "\{label}\{cap (snd im)}")
                     (zip [0 .. minus (length info.qiSorts) 1] info.qiSorts)
          mths : List String
          mths = methodsOf 0 info.qiPoints
          cohs : List String
          cohs = map (\c => lamChain (fst (methodBinders [] 0 c)) "⋆") info.qiEqs
      in Right (map (\f =>
           let flavor : String
               flavor = if f then "ElimP" else "Elim"
               cohsF : List String
               cohsF = if f then [] else cohs
           in (rng, closeApp apps
                      (layoutApp col (info.qiSort ++ flavor)
                                 (ps ++ mots ++ mths ++ cohsF ++ [var]))))
          flavors)
   where
    -- the Π-closure of a dependency-closed suffix rides INSIDE the
    -- motive and each method, exactly as it does at ℕ
    motive' : String
    motive' = case break (== '.') (unpack motive) of
                (_, _ :: rest) => ltrim (pack rest)
                _ => motive

    cap : String -> String
    cap x = case unpack x of
      (c :: cs) => pack (toUpper c :: cs)
      [] => x

    flavors : List Bool
    flavors = if evidentProp goal then [True, False] else [False, True]

    methodsOf : Nat -> List QIITCtor -> List String
    methodsOf _ [] = []
    methodsOf o (c :: rest) =
      let (bs, o') = methodBinders opts.optNames o c
      in lamChain bs "\{lams}?\{freshLabel taken "\{label}\{cap c.qcName}"}"
           :: methodsOf o' rest

  ||| The preferred form, and the fallback the trial falls back to when
  ||| the elaborator's own recovery does not fire.
  candidates : Range -> (preferBare : Bool) -> (bare, written : String)
            -> List (Range, String)
  candidates rng preferBare bare written =
    if preferBare then [(rng, bare), (rng, written)] else [(rng, written)]

  ||| The rewrite itself: the hole, re-minted at the goal the equation
  ||| states it also is. The switch closes by reflecting the equation
  ||| (el-reflect), which is why no eliminator is emitted.
  retype : FixTable -> (nms : List String) -> (n, p : Nat) -> Ty
        -> (label, txt : String) -> Either String (List (Range, String))
  retype tbl nms n p goal label txt =
    case h.dvrange of
      Nothing => Left "the hole has no source span to replace"
      Just rng =>
        if not (usesIndexTy (posOfIndex n p) goal)
          then Left "the goal does not mention \{nameOr nms p}, so rewriting it refines nothing"
          else Right [(rng, "(?\{label} : \{restate tbl nms n p (atomize txt) goal})")]

  ||| Why a type offers nothing of its own. A ν HAS an eliminator —
  ||| `out` — and saying it does not would be false: what it does not
  ||| have is a case analysis, since observing a stream refines no goal
  ||| (docs/NovaElaboration.txt, Restrictions). Everything else that
  ||| reaches here genuinely eliminates in no way at all: a universe, a
  ||| Π, a neutral.
  noEliminator : (px : Nat) -> String
  noEliminator px = case at px (toList v.hvCtxX) of
    Just (Elem.NuTy _) => "`out` at a ν OBSERVES rather than splits, so it refines no goal"
    _ => "this type has no eliminator"

  ||| No former of its own: the variable may still be eliminable by an
  ||| EQUATION of the context that has it as a side — reflection makes
  ||| that a change of ascription, with no eliminator at all.
  byEquation : FixTable -> Options -> List String -> DeclView -> String
            -> Range -> Ty -> List Ty -> List String -> (n, px : Nat) -> String
            -> Either String (List (Range, String))
  byEquation tbl opts taken h var rng goal tys nms n px label =
    let k = posOfIndex n px
        hyps = mapMaybe (\q => case at q tys of
                                 Just (Elem.EqTy l r _) =>
                                   if l == CtxVar (idxOfPos q px)
                                     then Just (q, r)
                                     else if r == CtxVar (idxOfPos q px)
                                            then Just (q, l)
                                            else Nothing
                                 _ => Nothing)
                        [0 .. minus n 1]
    in case reverse hyps of
         [] => Left "\{var} : \{noEliminator px}, and no equation of the context has it as a side"
         ((q, other) :: _) =>
           retype tbl nms n px goal label
             (prettyElemN tbl (toSnoc (take q (map (nameOr nms) [0 .. minus n 1]))) other)

-- ===== splicing =====

||| Replace `rng` in `src` with `txt`. Columns are CHARACTER offsets,
||| as the parser records them.
export
spliceAt : (src : String) -> Range -> (txt : String) -> String
spliceAt src rng txt =
  let ls = lines src
      sl = integerToNat (cast (max 0 rng.start.line))
      el = integerToNat (cast (max 0 rng.end.line))
      sc = integerToNat (cast (max 0 rng.start.column))
      ec = integerToNat (cast (max 0 rng.end.column))
      before = take sl ls
      after  = drop (S el) ls
      headL  = pack (take sc (unpack (fromMaybe "" (at sl ls))))
      tailL  = pack (drop ec (unpack (fromMaybe "" (at el ls))))
  in unlines (before ++ lines (headL ++ txt ++ tailL) ++ after)

-- ===== the command =====

||| A 1-based LINE:COL, as the report prints a hole's location.
export
parseLoc : String -> Maybe (Int, Int)
parseLoc s = case forget (split (== ':') s) of
  [l, c] => [| MkPair (map cast (parsePositive l)) (map cast (parsePositive c)) |]
  _ => Nothing

||| Flags after the variable: --deep, and the name/label slots in the
||| order the form declares them (docs/NovaElaboration.txt, Names). An
||| empty --name leaves that slot at its default.
export
parseOpts : List String -> Options
parseOpts = go defaultOptions
 where
  go : Options -> List String -> Options
  go o [] = o
  go o ("--deep" :: rest) = go ({ optDeep := True } o) rest
  go o ("--name" :: x :: rest) = go ({ optNames $= (++ [x]) } o) rest
  go o ("--label" :: x :: rest) = go ({ optLabels $= (++ [x]) } o) rest
  go o (_ :: rest) = go o rest

||| Labels a new hole of this item may NOT take: every OTHER hole of
||| the same item. The hole being replaced is not among them — its own
||| text is what goes away, so a retype may keep its label.
export
siblingLabels : List HoleView -> DeclView -> List String
siblingLabels hs h =
  [ bareLabel v.hvDecl.dvname
  | v <- hs
  , holeItem v.hvDecl.dvname == holeItem h.dvname
  , bareLabel v.hvDecl.dvname /= bareLabel h.dvname ]

||| WHAT THIS HOLE OFFERS: one entry per context variable that has an
||| elimination, with the variable's name, its type as the report would
||| render it, and whether the fully-iterated Σ split differs from the
||| one-step one (so a caller can offer both without knowing why).
|||
||| A variable a LATER entry shadows is not offered: it has no spelling
||| at the hole, since resolution takes the innermost binding of a name
||| (Name resolution). Neither is an anonymous entry.
export
offers : (taken : List String) -> (qiits : List QIITInfo) -> HoleView
      -> List (String, String, Bool)
offers taken qiits v =
  let tys = toList v.hvDecl.dvctx
      nms = toList v.hvDecl.dvenv
      n   = length tys
  in mapMaybe (offer tys nms n) [0 .. minus n 1]
 where
  offer : List Ty -> List String -> Nat -> Nat -> Maybe (String, String, Bool)
  offer tys nms n p =
    let var = nameOr nms p in
    if var == wildcard then Nothing
    else if resolveName v.hvDecl.dvenv var /= Just (posOfIndex n p) then Nothing
    else case eliminate defaultOptions taken qiits v var of
      Left _ => Nothing
      Right [] => Nothing
      Right ((_, shallow) :: _) =>
        let deep = case eliminate ({ optDeep := True } defaultOptions) taken qiits v var of
                     Right ((_, t) :: _) => t /= shallow
                     _ => False
        in Just ( var
                , prettyTyN v.hvFix (toSnoc (take p nms)) (fromMaybe TopTy (at p tys))
                , deep )

||| Does this hole's own span cover the given (0-based) position?
covers : (line, col : Int) -> DeclView -> Bool
covers line col h = case h.dvrange of
  Nothing => False
  Just r =>
    let p = MkPosition line col
    in r.start <= p && p <= r.end

||| The holes of the ROOT module: a command edits the file it was
||| given, so only that module's holes are addressable.
export
rootHoles : ElabReport -> List HoleView
rootHoles report = filter (\v => v.hvModule == "") report.holes

||| Every hole whose own `?x` span covers a position — an item macro
||| elaborates its bodies more than once, so one span may carry several,
||| at several contexts. Reading them is fine; REWRITING needs the one
||| (`holeAt`).
export
holesAt : ElabReport -> (line, col : Int) -> List HoleView
holesAt report line col = filter (\v => covers line col v.hvDecl) (rootHoles report)

||| ONE HOLE PER SPAN, said once: a caller that offers the action and a
||| caller that performs it give the same reason for refusing.
export
sharedSpanReason : (holes : Nat) -> String
sharedSpanReason n =
  "\{show n} holes share this span — an item macro elaborates its body more than once, and one text cannot serve every context"

||| The one hole whose own `?x` span covers a position.
|||
||| A span carrying several holes has no single answer, since one text
||| would have to serve every context (docs/NovaElaboration.txt,
||| Restrictions).
export
holeAt : ElabReport -> (line, col : Int) -> Either String HoleView
holeAt report line col =
  case holesAt report line col of
    [th] => Right th
    []   => Left "no hole at \{show (line + 1)}:\{show (col + 1)}"
    hs   => Left (sharedSpanReason (length hs))

||| The hole minted under a given Σ name, for a caller that already
||| chose one (the code action's resolve step, which addresses the
||| hole it offered rather than a position that may have moved).
export
holeNamed : ElabReport -> (sigName : String) -> Maybe HoleView
holeNamed report x =
  case filter (\v => v.hvDecl.dvname == x) (rootHoles report) of
    (v :: _) => Just v
    []       => Nothing

||| The definition an elimination had to READ THROUGH to find its
||| former: the display type is folded (`bisim s t`), classification
||| ran on the exposed one, and the elaborator will only follow the
||| same unfolding where the item CITES it. Naming it turns a trial
||| failure into the standard remedy.
export
unfoldHint : HoleView -> (var : String) -> Maybe String
unfoldHint v var = do
  k <- resolveName v.hvDecl.dvenv var
  let n = length (toList v.hvDecl.dvctx)
  folded <- at (posOfIndex n k) (toList v.hvDecl.dvctx)
  exposed <- at (posOfIndex n k) (toList v.hvCtxX)
  if show folded == show exposed then Nothing else Nothing <|> map fst (spineHead folded)

||| VERIFIED, NOT TRUSTED (docs/NovaElaboration.txt): the candidate is
||| re-parsed and re-elaborated before it is handed back, and rejected
||| unless every item still elaborates. New GOALS are expected — they
||| are the point — and so is a quot-elim's well-definedness
||| obligation; an item-level FAILURE is not, and that is how a form's
||| own restriction (squash-elim reaches only propositions) is enforced
||| without a second implementation of it.
|||
||| The trial runs from a temporary file beside the original, so its
||| imports resolve exactly as the original's do (`loadProgram`
||| resolves them against the file's own directory).
export
verify : (rootPath, content : String) -> IO (Maybe String)
verify rootPath content = do
  let tmp = rootPath ++ ".eliminate-trial"
  Right () <- writeFile tmp content
    | Left err => pure (Just "cannot write the trial file: \{show err}")
  units <- loadProgram tmp
  verdict <- case units of
    Left err => pure (Just (showLoadErr err))
    Right us => case (elabProgramReport us).errors of
      [] => pure Nothing
      es => pure (Just (joinBy "\n" (map (\e => let (_, _, m) = e in m) es)))
  _ <- removeFile tmp
  pure verdict

||| The edit an elimination makes, VERIFIED against the file it would
||| land in: the hole's own span, and the text that replaces it. The
||| caller already has the run that found the hole, so this re-runs the
||| elaborator exactly once — on the candidate.
export
eliminateEdit : (rootPath, src : String) -> (v : HoleView)
             -> (taken : List String) -> (qiits : List QIITInfo) -> (var : String)
             -> Options -> IO (Either String (Range, String))
eliminateEdit rootPath src v taken qiits var opts =
  case eliminate opts taken qiits v var of
    Left err => pure (Left err)
    Right cands => go cands
 where
  -- the first candidate that ELABORATES wins; the last one's failure
  -- is what the operator is told about, since the preferred forms
  -- differ only in what the elaborator was asked to recover
  note : String
  note = case unfoldHint v var of
    Just x => "\n  note: this reads \{var}'s type through \{x}; the item may need `using (\{x}.unfold)`"
    Nothing => ""

  go : List (Range, String) -> IO (Either String (Range, String))
  go [] = pure (Left "no form of this elimination elaborates")
  go ((rng, txt) :: rest) = do
    Nothing <- verify rootPath (spliceAt src rng txt)
      | Just err => case rest of
          [] => pure (Left "the elimination does not elaborate, so it is not offered:\n\{err}\{note}")
          _  => go rest
    pure (Right (rng, txt))

||| The `eliminate` command's body: elaborate the file, find the hole
||| whose own `?x` span covers the position, and return the file with
||| that span replaced.
export
eliminatePath : (rootPath : String) -> (line, col : Int) -> (var : String)
             -> Options -> IO (Either String String)
eliminatePath rootPath line col var opts = do
  Right units <- loadProgram rootPath
    | Left err => pure (Left (showLoadErr err))
  Right src <- readFile rootPath
    | Left err => pure (Left "cannot read '\{rootPath}': \{show err}")
  let report = elabProgramReport units
  case holeAt report line col of
    Left err => pure (Left err)
    Right v => do
      Right (rng, txt) <- eliminateEdit rootPath src v (siblingLabels report.holes v.hvDecl) report.qiits var opts
        | Left err => pure (Left (if isPrefixOf "the elimination" err
                                    then err
                                    else "\{rootPath}:\{show (line + 1)}:\{show (col + 1)}: \{err}"))
      pure (Right (spliceAt src rng txt))
