module Nova.Recovery

-- The spine-local argument-recovery ORACLE and the corpus SURVEY over
-- it — Phase 3 of docs/NovaPerfectSurface.txt, entered oracle-first:
-- this module measures, over an accepted Σ, which application
-- arguments a rigid first-order recoverer could reconstruct, BEFORE
-- any implicit-binder surface form is committed.
--
-- The oracle: at a def's application spine with candidate positions
-- elided (HOLES), walk the def's Π-telescope and solve each hole by
-- SIMULTANEOUS RIGID FIRST-ORDER MATCHING of the hole-bearing
-- instantiations against ground instances, from two sources:
--
--   * the spine's EXPECTED type, when the spine sits in a position
--     the bidirectional discipline gives a known type (the survey
--     tracks this flag purely syntactically, mirroring the ⇐/⇒ mode
--     inventory of docs/NovaElaboration.txt);
--   * the types of LATER EXPLICIT arguments that are themselves
--     INFERENCE forms (a λ or a ⋆ argument has no independently
--     known type, so it carries nothing).
--
-- Rigidity: a hole may bind only at a subterm SLOT — never in the
-- function position of an application (no higher-order unification,
-- no postponement, no backtracking; one deterministic pass). Holes
-- are encoded as Σ-references "?i", a shape no real Σ name can take.
--
-- Survey caveat, recorded: the ground instances stand in for the
-- inferred types the real elaborator would match against, so the
-- numbers are a CEILING — a site counted recoverable can still fail
-- in practice when the actual inferred type differs from the
-- instantiated domain up to computation. The verify pass of the
-- eventual implementation (elide-then-check at print time) is what
-- turns the ceiling into a guarantee.

import Data.List
import Data.Maybe
import Data.SnocList
import Data.String

import Nova.Kernel.Syntax
import Nova.Kernel.Subst

%default covering

-- ===== Holes =====

export
holeName : Nat -> String
holeName i = "?" ++ show i

export
holeE : Nat -> Elem
holeE i = SigVar (holeName i) [<]

export
holeView : String -> Maybe Nat
holeView nm = case unpack nm of
  ('?' :: ds) => parsePositive (pack ds)
  _ => Nothing

-- ===== The matcher =====
--
-- Pattern against ground, accumulating hole solutions; the pattern is
-- an instantiation of the same telescope as the ground, so mismatched
-- shapes only arise under an inconsistent candidate set. α-comparison
-- of core is structural (nameless), done here via Show.

public export
Sols : Type
Sols = List (Nat, Elem)

-- Strengthening: shift indices ≥ the cutoff DOWN by k; an index
-- inside the window (a crossed binder's variable) makes the term
-- inexpressible outside — the binding fails. This is what makes
-- matching under binders scope-correct: a hole binding captured at
-- depth k must strengthen by k to be usable at the spine.

mutual
  export
  strengthenE : (c, k : Nat) -> Elem -> Maybe Elem
  strengthenE c k e = case e of
    CtxVar i => if i < c then Just (CtxVar i)
                else if i < c + k then Nothing
                else Just (CtxVar (minus i k))
    SigVar nm sp => map (SigVar nm) (strengthenSp c k sp)
    ZeroElim t => map ZeroElim (strengthenE c k t)
    OneIntro => Just e
    NatIntro0 => Just e
    NatIntro1 t => map NatIntro1 (strengthenE c k t)
    NatElim z st t => [| NatElim (strengthenE c k z) (strengthenE (c + 2) k st) (strengthenE c k t) |]
    PiIntro b => map PiIntro (strengthenE (S c) k b)
    PiApp f a => [| PiApp (strengthenE c k f) (strengthenE c k a) |]
    Let d b => [| Let (strengthenE c k d) (strengthenE (c + 2) k b) |]
    SigmaIntro u v => [| SigmaIntro (strengthenE c k u) (strengthenE c k v) |]
    SigmaElim1 t => map SigmaElim1 (strengthenE c k t)
    SigmaElim2 t => map SigmaElim2 (strengthenE c k t)
    Inj1 t => map Inj1 (strengthenE c k t)
    Inj2 t => map Inj2 (strengthenE c k t)
    SumElim l r t => [| SumElim (strengthenE (S c) k l) (strengthenE (S c) k r) (strengthenE c k t) |]
    ZeroTy => Just e
    OneTy => Just e
    NatTy => Just e
    PiTy a b => [| PiTy (strengthenE c k a) (strengthenE (S c) k b) |]
    SigmaTy a b => [| SigmaTy (strengthenE c k a) (strengthenE (S c) k b) |]
    SumTy a b => [| SumTy (strengthenE c k a) (strengthenE c k b) |]
    EqTy l r ty => [| EqTy (strengthenE c k l) (strengthenE c k r) (strengthenT c k ty) |]
    QuotTy a r => [| QuotTy (strengthenE c k a) (strengthenE (c + 2) k r) |]
    Class t => map Class (strengthenE c k t)
    QuotElim f q => [| QuotElim (strengthenE (S c) k f) (strengthenE c k q) |]
    Squash ty => map Squash (strengthenT c k ty)
    Star => Just e
    QSortC sig j sp => map (QSortC sig j) (strengthenSp c k sp)
    QCtor sig j sp => map (QCtor sig j) (strengthenSp c k sp)
    QElim sig j mots mths sp w =>
      do mots' <- traverse (strengthenT c k) mots
         mths' <- traverse (strengthenE c k) mths
         sp' <- strengthenSp c k sp
         w' <- strengthenE c k w
         pure (QElim sig j mots' mths' sp' w')
    NuTy pl => map NuTy (strengthenP c k pl)
    Out t => map Out (strengthenE c k t)
    Corec pl a f x =>
      [| Corec (strengthenP c k pl) (strengthenE c k a) (strengthenE (S c) k f) (strengthenE c k x) |]

  strengthenSp : (c, k : Nat) -> SubNorm -> Maybe SubNorm
  strengthenSp c k [<] = Just [<]
  strengthenSp c k (xs :< x) = [| strengthenSp c k xs :< strengthenE c k x |]

  export
  strengthenT : (c, k : Nat) -> Ty -> Maybe Ty
  strengthenT c k ty = case ty of
    Ty.PiTy a b => [| Ty.PiTy (strengthenT c k a) (strengthenT (S c) k b) |]
    Ty.SigmaTy a b => [| Ty.SigmaTy (strengthenT c k a) (strengthenT (S c) k b) |]
    Ty.SumTy a b => [| Ty.SumTy (strengthenT c k a) (strengthenT c k b) |]
    El t => map El (strengthenE c k t)
    Prf t => map Prf (strengthenE c k t)
    Quotient a r => [| Quotient (strengthenT c k a) (strengthenE (c + 2) k r) |]
    Ty.SigVar nm sp => map (Ty.SigVar nm) (strengthenSp c k sp)
    QSort sig j sp => map (QSort sig j) (strengthenSp c k sp)
    Ty.NuTy pl => map Ty.NuTy (strengthenP c k pl)
    _ => Just ty

  strengthenP : (c, k : Nat) -> Poly -> Maybe Poly
  strengthenP c k pl = case pl of
    PHole => Just pl
    PConst a => map PConst (strengthenE c k a)
    PProd f g => [| PProd (strengthenP c k f) (strengthenP c k g) |]
    PSum f g => [| PSum (strengthenP c k f) (strengthenP c k g) |]
    PSigma a f => [| PSigma (strengthenE c k a) (strengthenP (S c) k f) |]
    PPi a f => [| PPi (strengthenE c k a) (strengthenP (S c) k f) |]

sameE : Elem -> Elem -> Bool
sameE a b = show a == show b

mutual
  ||| `applied` — the pattern sits in the function position of an
  ||| application: a hole here would be a flexible head, rejected by
  ||| the rigidity discipline. `k` — binders crossed since the spine:
  ||| a hole binding captured at depth k must STRENGTHEN by k (fail
  ||| if it mentions a crossed binder), so bindings stay
  ||| scope-correct at the spine.
  export
  mElem : (applied : Bool) -> (k : Nat) -> (pat : Elem) -> (ground : Elem) -> Sols -> Maybe Sols
  mElem app k (SigVar nm [<]) g sols =
    case holeView nm of
      Just i =>
        if app then Nothing else
          case strengthenE 0 k g of
            Nothing => Nothing
            Just g' => case lookup i sols of
              Just prev => if sameE prev g' then Just sols else Nothing
              Nothing => Just ((i, g') :: sols)
      Nothing => case g of
        SigVar nm' [<] => if nm == nm' then Just sols else Nothing
        _ => Nothing
  mElem app k (SigVar nm sp) g sols =
    case g of
      SigVar nm' sp' => if nm == nm' then mSub k sp sp' sols else Nothing
      _ => Nothing
  mElem app k (CtxVar n) g sols =
    case g of CtxVar n' => if n == n' then Just sols else Nothing; _ => Nothing
  mElem app k (ZeroElim t) g sols =
    case g of ZeroElim t' => mElem False k t t' sols; _ => Nothing
  mElem app k OneIntro g sols =
    case g of OneIntro => Just sols; _ => Nothing
  mElem app k NatIntro0 g sols =
    case g of NatIntro0 => Just sols; _ => Nothing
  mElem app k (NatIntro1 t) g sols =
    case g of NatIntro1 t' => mElem False k t t' sols; _ => Nothing
  mElem app k (NatElim z st t) g sols =
    case g of
      NatElim z' st' t' => mElem False k z z' sols >>= mElem False (k + 2) st st' >>= mElem False k t t'
      _ => Nothing
  mElem app k (PiIntro b) g sols =
    case g of PiIntro b' => mElem False (S k) b b' sols; _ => Nothing
  mElem app k (PiApp f a) g sols =
    case g of
      PiApp f' a' => mElem True k f f' sols >>= mElem False k a a'
      _ => Nothing
  mElem app k (Let d b) g sols =
    case g of Let d' b' => mElem False k d d' sols >>= mElem False (k + 2) b b'; _ => Nothing
  mElem app k (SigmaIntro u v) g sols =
    case g of SigmaIntro u' v' => mElem False k u u' sols >>= mElem False k v v'; _ => Nothing
  mElem app k (SigmaElim1 t) g sols =
    case g of SigmaElim1 t' => mElem False k t t' sols; _ => Nothing
  mElem app k (SigmaElim2 t) g sols =
    case g of SigmaElim2 t' => mElem False k t t' sols; _ => Nothing
  mElem app k (Inj1 t) g sols =
    case g of Inj1 t' => mElem False k t t' sols; _ => Nothing
  mElem app k (Inj2 t) g sols =
    case g of Inj2 t' => mElem False k t t' sols; _ => Nothing
  mElem app k (SumElim l r t) g sols =
    case g of
      SumElim l' r' t' => mElem False (S k) l l' sols >>= mElem False (S k) r r' >>= mElem False k t t'
      _ => Nothing
  mElem app k ZeroTy g sols = case g of ZeroTy => Just sols; _ => Nothing
  mElem app k OneTy g sols = case g of OneTy => Just sols; _ => Nothing
  mElem app k NatTy g sols = case g of NatTy => Just sols; _ => Nothing
  mElem app k (PiTy a b) g sols =
    case g of PiTy a' b' => mElem False k a a' sols >>= mElem False (S k) b b'; _ => Nothing
  mElem app k (SigmaTy a b) g sols =
    case g of SigmaTy a' b' => mElem False k a a' sols >>= mElem False (S k) b b'; _ => Nothing
  mElem app k (SumTy a b) g sols =
    case g of SumTy a' b' => mElem False k a a' sols >>= mElem False k b b'; _ => Nothing
  mElem app k (EqTy l r ty) g sols =
    case g of
      EqTy l' r' ty' => mElem False k l l' sols >>= mElem False k r r' >>= mTy k ty ty'
      _ => Nothing
  mElem app k (QuotTy a r) g sols =
    case g of QuotTy a' r' => mElem False k a a' sols >>= mElem False (k + 2) r r'; _ => Nothing
  mElem app k (Class t) g sols =
    case g of Class t' => mElem False k t t' sols; _ => Nothing
  mElem app k (QuotElim f q) g sols =
    case g of QuotElim f' q' => mElem False (S k) f f' sols >>= mElem False k q q'; _ => Nothing
  mElem app k (Squash ty) g sols =
    case g of Squash ty' => mTy k ty ty' sols; _ => Nothing
  mElem app k Star g sols = case g of Star => Just sols; _ => Nothing
  mElem app k (QSortC sig j sp) g sols =
    case g of
      QSortC sig' j' sp' =>
        if j == j' && show sig == show sig' then mSub k sp sp' sols else Nothing
      _ => Nothing
  mElem app k (QCtor sig j sp) g sols =
    case g of
      QCtor sig' j' sp' =>
        if j == j' && show sig == show sig' then mSub k sp sp' sols else Nothing
      _ => Nothing
  mElem app k (QElim sig j mots mths sp w) g sols =
    case g of
      QElim sig' j' mots' mths' sp' w' =>
        if j == j' && show sig == show sig'
          then mTys k mots mots' sols >>= mElems k mths mths' >>= mSub k sp sp' >>= mElem False k w w'
          else Nothing
      _ => Nothing
  mElem app k (NuTy p) g sols =
    case g of NuTy p' => mPoly k p p' sols; _ => Nothing
  mElem app k (Out t) g sols =
    case g of Out t' => mElem False k t t' sols; _ => Nothing
  mElem app k (Corec p a f x) g sols =
    case g of
      Corec p' a' f' x' =>
        mPoly k p p' sols >>= mElem False k a a' >>= mElem False (S k) f f' >>= mElem False k x x'
      _ => Nothing

  mElems : (k : Nat) -> List Elem -> List Elem -> Sols -> Maybe Sols
  mElems k [] [] sols = Just sols
  mElems k (x :: xs) (y :: ys) sols = mElem False k x y sols >>= mElems k xs ys
  mElems k _ _ _ = Nothing

  mTys : (k : Nat) -> List Ty -> List Ty -> Sols -> Maybe Sols
  mTys k [] [] sols = Just sols
  mTys k (x :: xs) (y :: ys) sols = mTy k x y sols >>= mTys k xs ys
  mTys k _ _ _ = Nothing

  mSub : (k : Nat) -> SubNorm -> SubNorm -> Sols -> Maybe Sols
  mSub k [<] [<] sols = Just sols
  mSub k (xs :< x) (ys :< y) sols = mSub k xs ys sols >>= mElem False k x y
  mSub k _ _ _ = Nothing

  ||| The 𝕌-code of a type in the image of El-decoding — the mixed-El
  ||| case of the ↓ loop, oracle-side: a bare hole under El may bind
  ||| to code(B) when B decodes (ty-el-nat, ty-el-pi, …).
  codeOfTy : Ty -> Maybe Elem
  codeOfTy Ty.ZeroTy = Just Elem.ZeroTy
  codeOfTy Ty.OneTy = Just Elem.OneTy
  codeOfTy Ty.NatTy = Just Elem.NatTy
  codeOfTy (Ty.PiTy a b) = [| Elem.PiTy (codeOfTy a) (codeOfTy b) |]
  codeOfTy (Ty.SigmaTy a b) = [| Elem.SigmaTy (codeOfTy a) (codeOfTy b) |]
  codeOfTy (Ty.SumTy a b) = [| Elem.SumTy (codeOfTy a) (codeOfTy b) |]
  codeOfTy (Quotient a r) = map (\c => QuotTy c r) (codeOfTy a)
  codeOfTy (El t) = Just t
  codeOfTy (Ty.NuTy p) = Just (Elem.NuTy p)
  codeOfTy _ = Nothing

  export
  mTy : (k : Nat) -> Ty -> Ty -> Sols -> Maybe Sols
  mTy k Ty.ZeroTy g sols = case g of Ty.ZeroTy => Just sols; _ => Nothing
  mTy k Ty.OneTy g sols = case g of Ty.OneTy => Just sols; _ => Nothing
  mTy k Ty.NatTy g sols = case g of Ty.NatTy => Just sols; _ => Nothing
  mTy k UniverseTy g sols = case g of UniverseTy => Just sols; _ => Nothing
  mTy k PropTy g sols = case g of PropTy => Just sols; _ => Nothing
  mTy k (Ty.PiTy a b) g sols =
    case g of Ty.PiTy a' b' => mTy k a a' sols >>= mTy (S k) b b'; _ => Nothing
  mTy k (Ty.SigmaTy a b) g sols =
    case g of Ty.SigmaTy a' b' => mTy k a a' sols >>= mTy (S k) b b'; _ => Nothing
  mTy k (Ty.SumTy a b) g sols =
    case g of Ty.SumTy a' b' => mTy k a a' sols >>= mTy k b b'; _ => Nothing
  mTy k (El t) g sols = case g of
    El t' => mElem False k t t' sols
    -- a bare hole under El against a DECODED rigid type binds to its
    -- code (the matching-up-to-El-decoding of the ↓ loop's step 7)
    _ => case t of
      SigVar nm [<] => case holeView nm of
        Just _ => case codeOfTy g of
          Just c => mElem False k t c sols
          Nothing => Nothing
        Nothing => Nothing
      _ => Nothing
  mTy k (Prf t) g sols = case g of Prf t' => mElem False k t t' sols; _ => Nothing
  mTy k (Quotient a r) g sols =
    case g of Quotient a' r' => mTy k a a' sols >>= mElem False (k + 2) r r'; _ => Nothing
  mTy k (Ty.SigVar nm sp) g sols =
    case g of
      Ty.SigVar nm' sp' => if nm == nm' then mSub k sp sp' sols else Nothing
      _ => Nothing
  mTy k (QSort sig j sp) g sols =
    case g of
      QSort sig' j' sp' =>
        if j == j' && show sig == show sig' then mSub k sp sp' sols else Nothing
      _ => Nothing
  mTy k (Ty.NuTy p) g sols = case g of Ty.NuTy p' => mPoly k p p' sols; _ => Nothing

  mPoly : (k : Nat) -> Poly -> Poly -> Sols -> Maybe Sols
  mPoly k PHole g sols = case g of PHole => Just sols; _ => Nothing
  mPoly k (PConst a) g sols = case g of PConst a' => mElem False k a a' sols; _ => Nothing
  mPoly k (PProd f h) g sols =
    case g of PProd f' h' => mPoly k f f' sols >>= mPoly k h h'; _ => Nothing
  mPoly k (PSum f h) g sols =
    case g of PSum f' h' => mPoly k f f' sols >>= mPoly k h h'; _ => Nothing
  mPoly k (PSigma a f) g sols =
    case g of PSigma a' f' => mElem False k a a' sols >>= mPoly (S k) f f'; _ => Nothing
  mPoly k (PPi a f) g sols =
    case g of PPi a' f' => mElem False k a a' sols >>= mPoly (S k) f f'; _ => Nothing

-- ===== Telescopes =====

||| Peel the syntactic Π-telescope of a CLOSED Σ-type: the domains (as
||| written, each under its predecessors) and the residual type.
export
teleOf : Ty -> (List Ty, Ty)
teleOf (Ty.PiTy a b) = let (ds, r) = teleOf b in (a :: ds, r)
teleOf ty = ([], ty)

||| The substitution [t₀, …, tₖ₋₁] into a closed telescope prefix.
export
prefixSub : List Elem -> Sub
prefixSub = foldl Ext Terminal

||| Is the (core) argument an INFERENCE form — one whose type the
||| elaborator knows without the domain? Checking-only forms (λ,
||| pairs, ⋆ — every erased proof —, injections, class, 𝟘-elim,
||| corec) carry nothing.
inferForm : Elem -> Bool
inferForm e = case e of
  PiIntro _ => False
  SigmaIntro _ _ => False
  Star => False
  Inj1 _ => False
  Inj2 _ => False
  Class _ => False
  ZeroElim _ => False
  Corec _ _ _ _ => False
  QCtor _ _ _ => False
  _ => True

-- ===== The per-site oracle =====

||| One application spine of a Σ-definition, as found in the corpus.
public export
record SpineUse where
  constructor MkSpineUse
  suHead : String
  suArgs : List Elem
  ||| the spine sits where the bidirectional pass KNOWS the expected
  ||| type (⇐ position)
  suKnown : Bool

||| Which of the candidate positions does the oracle recover at this
||| site? Returns the positions SOLVED. Candidates beyond the applied
||| prefix are ignored here (reported as short-arity by the caller).
solveSite : (doms : List Ty) -> (residual : Ty) -> (cands : List Nat) -> SpineUse -> List Nat
solveSite doms residual cands (MkSpineUse _ args known) =
  let m = min (length doms) (length args)
      liveCands = filter (< m) cands
      pats = map (\(i, a) => if i `elem` liveCands then holeE i else a)
                 (zip [0 .. minus (length args) 1] args)
      sols0 = the Sols []
      -- source 1: the expected type — usable only when the whole
      -- telescope is applied syntactically (otherwise the residual
      -- type here is not the spine's type)
      sols1 = if known && length args == length doms
                then fromMaybe sols0 (mTy 0 (substTy residual (prefixSub pats))
                                          (substTy residual (prefixSub args)) sols0)
                else sols0
      -- source 2: later explicit inference-form arguments, LEFT TO
      -- RIGHT (solutions accumulate; each domain pattern uses the
      -- prefix of pattern entries)
      sols2 = goArgs 0 doms pats args sols1
  in map fst sols2
 where
  goArgs : Nat -> List Ty -> List Elem -> List Elem -> Sols -> Sols
  goArgs j (d :: ds) pats args sols =
    let sols' =
          if not (j `elem` cands) && maybe False inferForm (getAt j args)
            then let patD = substTy d (prefixSub (take j pats))
                     grdD = substTy d (prefixSub (take j args))
                 in fromMaybe sols (mTy 0 patD grdD sols)
            else sols
    in goArgs (S j) ds pats args sols'
  goArgs _ [] _ _ sols = sols

-- ===== The Σ walk: collecting use sites =====
--
-- The `known` flag mirrors the mode inventory of
-- docs/NovaElaboration.txt: checked positions propagate True,
-- inference positions (application heads, projection and out
-- scrutinees, ⊎-/quot-elim scrutinees, let definientia) reset it.

spineView : Elem -> (Elem, List Elem)
spineView e = go e []
 where
  go : Elem -> List Elem -> (Elem, List Elem)
  go (PiApp f a) acc = go f (a :: acc)
  go h acc = (h, acc)

mutual
  walkE : (known : Bool) -> Elem -> List SpineUse -> List SpineUse
  walkE known e acc = case e of
    PiApp _ _ =>
      let (h, args) = spineView e
          acc' = foldl (\a, arg => walkE True arg a) acc args
      in case h of
           SigVar nm [<] => MkSpineUse nm args known :: acc'
           _ => walkE False h acc'
    CtxVar _ => acc
    SigVar nm sp => foldl (\a, x => walkE True x a) acc (toList sp)
    ZeroElim t => walkE True t acc
    OneIntro => acc
    NatIntro0 => acc
    NatIntro1 t => walkE True t acc
    NatElim z s t => walkE True z (walkE True s (walkE True t acc))
    PiIntro b => walkE True b acc
    Let d b => walkE False d (walkE known b acc)
    SigmaIntro u v => walkE True u (walkE True v acc)
    SigmaElim1 t => walkE False t acc
    SigmaElim2 t => walkE False t acc
    Inj1 t => walkE True t acc
    Inj2 t => walkE True t acc
    SumElim l r t => walkE True l (walkE True r (walkE False t acc))
    ZeroTy => acc
    OneTy => acc
    NatTy => acc
    PiTy a b => walkE True a (walkE True b acc)
    SigmaTy a b => walkE True a (walkE True b acc)
    SumTy a b => walkE True a (walkE True b acc)
    EqTy l r ty => walkE True l (walkE True r (walkT ty acc))
    QuotTy a r => walkE True a (walkE True r acc)
    Class t => walkE True t acc
    QuotElim f q => walkE True f (walkE False q acc)
    Squash ty => walkT ty acc
    Star => acc
    QSortC _ _ sp => foldl (\a, x => walkE True x a) acc (toList sp)
    QCtor _ _ sp => foldl (\a, x => walkE True x a) acc (toList sp)
    QElim _ _ mots mths sp w =>
      let acc1 = foldl (\a, t => walkT t a) acc mots
          acc2 = foldl (\a, m => walkE True m a) acc1 mths
          acc3 = foldl (\a, x => walkE True x a) acc2 (toList sp)
      in walkE True w acc3
    NuTy p => walkP p acc
    Out t => walkE False t acc
    Corec p a f x => walkP p (walkE True a (walkE True f (walkE True x acc)))

  walkT : Ty -> List SpineUse -> List SpineUse
  walkT ty acc = case ty of
    Ty.PiTy a b => walkT a (walkT b acc)
    Ty.SigmaTy a b => walkT a (walkT b acc)
    Ty.SumTy a b => walkT a (walkT b acc)
    El t => walkE True t acc
    Prf t => walkE True t acc
    Quotient a r => walkT a (walkE True r acc)
    Ty.SigVar _ sp => foldl (\a, x => walkE True x a) acc (toList sp)
    QSort _ _ sp => foldl (\a, x => walkE True x a) acc (toList sp)
    Ty.NuTy p => walkP p acc
    _ => acc

  walkP : Poly -> List SpineUse -> List SpineUse
  walkP p acc = case p of
    PHole => acc
    PConst a => walkE True a acc
    PProd f g => walkP f (walkP g acc)
    PSum f g => walkP f (walkP g acc)
    PSigma a f => walkE True a (walkP f acc)
    PPi a f => walkE True a (walkP f acc)

||| Every def-application spine in an accepted Σ (bodies and types).
collectUses : Sig -> List SpineUse
collectUses sig = foldl entry [] (toList sig)
 where
  entry : List SpineUse -> SigEntry -> List SpineUse
  entry acc (SigDef _ _ body ty) = walkE True body (walkT ty acc)
  entry acc (SigTyDef _ _ ty) = walkT ty acc
  entry acc (SigDecl _ _ ty) = walkT ty acc
  entry acc _ = acc

-- ===== The per-def fixpoint and the report =====

public export
record DefStat where
  constructor MkDefStat
  dsName : String
  dsArity : Nat
  ||| final implicitizable positions
  dsImplicit : List Nat
  dsSites : Nat
  ||| elidable argument occurrences across all sites (final set)
  dsElidable : Nat
  ||| positions blocked because some site applies the def too
  ||| shallowly to reach them
  dsShortArity : Nat

||| Iterate the candidate set: a position survives iff every site
||| covers it (applies the def at least that far) and the oracle
||| solves it at every site. Dropping a position turns its argument
||| into a SOURCE elsewhere, so iteration is monotone and converges.
defStat : (name : String) -> (ty : Ty) -> List SpineUse -> Maybe DefStat
defStat name ty uses =
  if arity == 0 then Nothing else
    let positions = [0 .. minus arity 1]
        shortBlocked = filter (\i => any (\u => length u.suArgs <= i) uses) positions
        start = filter (\i => not (i `elem` shortBlocked)) positions
        final = fix start
        elid = sum (map (\u => length (intersect final (solveSite doms residual final u))) uses)
    in Just (MkDefStat name arity final (length uses) elid (length shortBlocked))
 where
  doms : List Ty
  doms = fst (teleOf ty)

  residual : Ty
  residual = snd (teleOf ty)

  arity : Nat
  arity = length doms

  fix : List Nat -> List Nat
  fix cands =
    let cands' = filter (\i => all (\u => i `elem` solveSite doms residual cands u) uses) cands
    in if length cands' == length cands then cands else fix cands'

||| The per-def survey statistics over an accepted Σ (defs with at
||| least one use site).
export
surveyStats : Sig -> List DefStat
surveyStats sig =
  let uses = collectUses sig
      defs = mapMaybe (\e => case e of
                               SigDef _ nm _ ty => Just (nm, ty)
                               _ => Nothing) (toList sig)
      stats = mapMaybe (\(nm, ty) => defStat nm ty (filter (\u => u.suHead == nm) uses)) defs
  in filter (\s => s.dsSites > 0) stats

||| The survey's CANDIDATE table: used defs with a nonempty
||| implicitizable set — the implicitize mode's input
||| (docs/NovaPerfectSurface.txt, Phase 3c). Ceiling numbers: the
||| trial pass measures the real recovery per site.
export
implicitizables : Sig -> List (String, List Nat)
implicitizables sig =
  map (\s => (s.dsName, s.dsImplicit))
      (filter (\s => not (null s.dsImplicit)) (surveyStats sig))

||| The survey over an accepted Σ: per def, the implicitizable
||| positions and the elidable-occurrence yield.
export
surveyReport : Sig -> String
surveyReport sig =
  let uses = collectUses sig
      defs = mapMaybe (\e => case e of
                               SigDef _ nm _ ty => Just (nm, ty)
                               _ => Nothing) (toList sig)
      stats = mapMaybe (\(nm, ty) => defStat nm ty (filter (\u => u.suHead == nm) uses)) defs
      used = filter (\s => s.dsSites > 0) stats
      winners = filter (\s => not (null s.dsImplicit)) used
      sorted = sortBy (\a, b => compare (b.dsElidable, a.dsName) (a.dsElidable, b.dsName)) winners
      totPos = sum (map dsArity used)
      totImp = sum (map (length . dsImplicit) winners)
      totOcc = sum (map (\u => length u.suArgs) uses)
      totElid = sum (map dsElidable winners)
  in unlines $
    [ "argument-recovery survey (docs/NovaPerfectSurface.txt, phase 3 — oracle ceiling):"
    , "  defs with use sites: \{show (length used)}  binder positions: \{show totPos}"
    , "  implicitizable positions: \{show totImp}  (defs with at least one: \{show (length winners)})"
    , "  argument occurrences: \{show totOcc}  elidable: \{show totElid}"
    , ""
    , "per def (position set, sites, elidable occurrences):"
    ] ++
    map (\s => "  \{s.dsName}  arity \{show s.dsArity}  implicit \{show s.dsImplicit}" ++
               "  sites \{show s.dsSites}  elides \{show s.dsElidable}" ++
               (if s.dsShortArity > 0 then "  (short-arity blocked: \{show s.dsShortArity})" else ""))
        sorted

-- ===== Hole detection (for the elaborator's spine recovery) =====

mutual
  export
  hasHolesE : Elem -> Bool
  hasHolesE e = case e of
    SigVar nm sp => isJust (holeView nm) || any hasHolesE (toList sp)
    CtxVar _ => False
    ZeroElim t => hasHolesE t
    OneIntro => False
    NatIntro0 => False
    NatIntro1 t => hasHolesE t
    NatElim z s t => hasHolesE z || hasHolesE s || hasHolesE t
    PiIntro b => hasHolesE b
    PiApp f a => hasHolesE f || hasHolesE a
    Let d b => hasHolesE d || hasHolesE b
    SigmaIntro u v => hasHolesE u || hasHolesE v
    SigmaElim1 t => hasHolesE t
    SigmaElim2 t => hasHolesE t
    Inj1 t => hasHolesE t
    Inj2 t => hasHolesE t
    SumElim l r t => hasHolesE l || hasHolesE r || hasHolesE t
    ZeroTy => False
    OneTy => False
    NatTy => False
    PiTy a b => hasHolesE a || hasHolesE b
    SigmaTy a b => hasHolesE a || hasHolesE b
    SumTy a b => hasHolesE a || hasHolesE b
    EqTy l r ty => hasHolesE l || hasHolesE r || hasHolesT ty
    QuotTy a r => hasHolesE a || hasHolesE r
    Class t => hasHolesE t
    QuotElim f q => hasHolesE f || hasHolesE q
    Squash ty => hasHolesT ty
    Star => False
    QSortC _ _ sp => any hasHolesE (toList sp)
    QCtor _ _ sp => any hasHolesE (toList sp)
    QElim _ _ mots mths sp w =>
      any hasHolesT mots || any hasHolesE mths || any hasHolesE (toList sp) || hasHolesE w
    NuTy p => hasHolesP p
    Out t => hasHolesE t
    Corec p a f x => hasHolesP p || hasHolesE a || hasHolesE f || hasHolesE x

  export
  hasHolesT : Ty -> Bool
  hasHolesT ty = case ty of
    Ty.PiTy a b => hasHolesT a || hasHolesT b
    Ty.SigmaTy a b => hasHolesT a || hasHolesT b
    Ty.SumTy a b => hasHolesT a || hasHolesT b
    El t => hasHolesE t
    Prf t => hasHolesE t
    Quotient a r => hasHolesT a || hasHolesE r
    Ty.SigVar nm sp => isJust (holeView nm) || any hasHolesE (toList sp)
    QSort _ _ sp => any hasHolesE (toList sp)
    Ty.NuTy p => hasHolesP p
    _ => False

  export
  hasHolesP : Poly -> Bool
  hasHolesP p = case p of
    PHole => False
    PConst a => hasHolesE a
    PProd f g => hasHolesP f || hasHolesP g
    PSum f g => hasHolesP f || hasHolesP g
    PSigma a f => hasHolesE a || hasHolesP f
    PPi a f => hasHolesE a || hasHolesP f

||| Substitute solved holes into a term (unsolved holes stay).
export
plugE : Sols -> Elem -> Elem
plugE sols e = case e of
  SigVar nm [<] => case holeView nm of
    Just i => fromMaybe e (lookup i sols)
    Nothing => e
  _ => e

||| Rebuild a Π-tail: the unconsumed domains (as written, each under
||| its predecessors) closed over the residual — the type of a
||| partial application, before instantiation.
export
rebuildTail : List Ty -> Ty -> Ty
rebuildTail [] r = r
rebuildTail (d :: ds) r = Ty.PiTy d (rebuildTail ds r)
