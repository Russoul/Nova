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
import Nova.Elaboration.Beta

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

-- ===== Skeleton-freedom =====
--
-- A SYNTHESIZED annotation (a recovered motive, an inferred ≡-domain)
-- ships with an empty skeleton, so it may not contain STUCK
-- ELIMINATORS — bare core ℕ-elim/⊎-elim/quot-elim need kernel
-- payloads (motives, well-definedness) an empty skeleton cannot
-- carry. (QElim and Corec carry their annotations inline in core and
-- are fine.) Elision verdicts and the elided rules both require this.

mutual
  export
  skelFreeE : Elem -> Bool
  skelFreeE e = case e of
    NatElim _ _ _ => False
    SumElim _ _ _ => False
    QuotElim _ _ => False
    CtxVar _ => True
    SigVar _ sp => all skelFreeE (toList sp)
    ZeroElim t => skelFreeE t
    OneIntro => True
    NatIntro0 => True
    NatIntro1 t => skelFreeE t
    PiIntro b => skelFreeE b
    PiApp f a => skelFreeE f && skelFreeE a
    Let d b => skelFreeE d && skelFreeE b
    SigmaIntro u v => skelFreeE u && skelFreeE v
    SigmaElim1 t => skelFreeE t
    SigmaElim2 t => skelFreeE t
    Inj1 t => skelFreeE t
    Inj2 t => skelFreeE t
    ZeroTy => True
    OneTy => True
    NatTy => True
    UniverseTy => True
    PropTy => True
    TopTy => True
    PiTy a b => skelFreeE a && skelFreeE b
    SigmaTy a b => skelFreeE a && skelFreeE b
    SumTy a b => skelFreeE a && skelFreeE b
    EqTy l r ty => skelFreeE l && skelFreeE r && skelFreeT ty
    QuotTy a r => skelFreeE a && skelFreeE r
    Class t => skelFreeE t
    Squash ty => skelFreeT ty
    Star => True
    QSort _ _ sp => all skelFreeE (toList sp)
    QCtor _ _ sp => all skelFreeE (toList sp)
    QElim _ _ mots mths sp w =>
      all skelFreeT mots && all skelFreeE mths && all skelFreeE (toList sp) && skelFreeE w
    NuTy p => skelFreeP p
    Out t => skelFreeE t
    Corec p a f x => skelFreeP p && skelFreeE a && skelFreeE f && skelFreeE x

  export
  ||| One sort (El retired): a code type carries eliminators exactly
  ||| where the element walk finds them — no former-only shortcut.
  skelFreeT : Ty -> Bool
  skelFreeT = skelFreeE

  skelFreeP : Poly -> Bool
  skelFreeP p = case p of
    PHole => True
    PConst a => skelFreeE a
    PProd f g => skelFreeP f && skelFreeP g
    PSum f g => skelFreeP f && skelFreeP g
    PSigma a f => skelFreeE a && skelFreeP f
    PPi a f => skelFreeE a && skelFreeP f

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

-- The traversal is shared between STRENGTHENING (under-depth
-- variables fail, spine-level ones shift down) and the PATTERN
-- ABSTRACTION (under-depth variables remap to fresh λ binders): both
-- are variable POLICIES over one structural walk. The policy sees
-- the occurrence's internal depth d and the index m RELATIVE to the
-- walk's start (m = i - d).
mutual
  export
  varMapE : (vf : (d : Nat) -> Nat -> Maybe Elem) -> (c : Nat) -> Elem -> Maybe Elem
  varMapE vf c e = case e of
    CtxVar i => if i < c then Just (CtxVar i) else vf c (minus i c)
    SigVar nm sp => map (SigVar nm) (varMapSp vf c sp)
    ZeroElim t => map ZeroElim (varMapE vf c t)
    OneIntro => Just e
    NatIntro0 => Just e
    NatIntro1 t => map NatIntro1 (varMapE vf c t)
    NatElim z st t => [| NatElim (varMapE vf c z) (varMapE vf (c + 2) st) (varMapE vf c t) |]
    PiIntro b => map PiIntro (varMapE vf (S c) b)
    PiApp f a => [| PiApp (varMapE vf c f) (varMapE vf c a) |]
    Let d b => [| Let (varMapE vf c d) (varMapE vf (c + 2) b) |]
    SigmaIntro u v => [| SigmaIntro (varMapE vf c u) (varMapE vf c v) |]
    SigmaElim1 t => map SigmaElim1 (varMapE vf c t)
    SigmaElim2 t => map SigmaElim2 (varMapE vf c t)
    Inj1 t => map Inj1 (varMapE vf c t)
    Inj2 t => map Inj2 (varMapE vf c t)
    SumElim l r t => [| SumElim (varMapE vf (S c) l) (varMapE vf (S c) r) (varMapE vf c t) |]
    ZeroTy => Just e
    OneTy => Just e
    NatTy => Just e
    UniverseTy => Just e
    PropTy => Just e
    TopTy => Just e
    PiTy a b => [| PiTy (varMapE vf c a) (varMapE vf (S c) b) |]
    SigmaTy a b => [| SigmaTy (varMapE vf c a) (varMapE vf (S c) b) |]
    SumTy a b => [| SumTy (varMapE vf c a) (varMapE vf c b) |]
    EqTy l r ty => [| EqTy (varMapE vf c l) (varMapE vf c r) (varMapT vf c ty) |]
    QuotTy a r => [| QuotTy (varMapE vf c a) (varMapE vf (c + 2) r) |]
    Class t => map Class (varMapE vf c t)
    QuotElim f q => [| QuotElim (varMapE vf (S c) f) (varMapE vf c q) |]
    Squash ty => map Squash (varMapT vf c ty)
    Star => Just e
    QSort sig j sp => map (QSort sig j) (varMapSp vf c sp)
    QCtor sig j sp => map (QCtor sig j) (varMapSp vf c sp)
    QElim sig j mots mths sp w =>
      do mots' <- traverse (varMapT vf c) mots
         mths' <- traverse (varMapE vf c) mths
         sp' <- varMapSp vf c sp
         w' <- varMapE vf c w
         pure (QElim sig j mots' mths' sp' w')
    NuTy pl => map NuTy (varMapP vf c pl)
    Out t => map Out (varMapE vf c t)
    Corec pl a f x =>
      [| Corec (varMapP vf c pl) (varMapE vf c a) (varMapE vf (S c) f) (varMapE vf c x) |]

  varMapSp : (vf : (d : Nat) -> Nat -> Maybe Elem) -> (c : Nat) -> SubNorm -> Maybe SubNorm
  varMapSp vf c [<] = Just [<]
  varMapSp vf c (xs :< x) = [| varMapSp vf c xs :< varMapE vf c x |]

  ||| One sort (El retired): a former-only walk here would leave the
  ||| indices inside a CODE type (an application spine, a bound code)
  ||| untouched — silent capture under strengthening/weakening.
  export
  varMapT : (vf : (d : Nat) -> Nat -> Maybe Elem) -> (c : Nat) -> Ty -> Maybe Ty
  varMapT = varMapE

  varMapP : (vf : (d : Nat) -> Nat -> Maybe Elem) -> (c : Nat) -> Poly -> Maybe Poly
  varMapP vf c pl = case pl of
    PHole => Just pl
    PConst a => map PConst (varMapE vf c a)
    PProd f g => [| PProd (varMapP vf c f) (varMapP vf c g) |]
    PSum f g => [| PSum (varMapP vf c f) (varMapP vf c g) |]
    PSigma a f => [| PSigma (varMapE vf c a) (varMapP vf (S c) f) |]
    PPi a f => [| PPi (varMapE vf c a) (varMapP vf (S c) f) |]

||| the classic strengthening policy: a crossed binder's variable
||| fails; a spine-level one shifts down by k
strengthenVf : (k : Nat) -> (d : Nat) -> Nat -> Maybe Elem
strengthenVf k d m = if m < k then Nothing else Just (CtxVar (d + minus m k))

export
strengthenE : (c, k : Nat) -> Elem -> Maybe Elem
strengthenE c k = varMapE (strengthenVf k) c

export
strengthenT : (c, k : Nat) -> Ty -> Maybe Ty
strengthenT c k = varMapT (strengthenVf k) c

strengthenSp : (c, k : Nat) -> SubNorm -> Maybe SubNorm
strengthenSp c k = varMapSp (strengthenVf k) c

strengthenP : (c, k : Nat) -> Poly -> Maybe Poly
strengthenP c k = varMapP (strengthenVf k) c

sameE : Elem -> Elem -> Bool
sameE a b = show a == show b

||| a hole applied to bound variables: (hole index, the applied
||| variable indices in APPLICATION order — first-applied outermost)
patView : Elem -> List Nat -> Maybe (Nat, List Nat)
patView (PiApp f (CtxVar c)) acc = patView f (c :: acc)
patView (SigVar nm [<]) acc =
  case holeView nm of
    Just i => case acc of
                [] => Nothing
                _ => Just (i, acc)
    Nothing => Nothing
patView _ _ = Nothing

allDistinct : List Nat -> Bool
allDistinct [] = True
allDistinct (x :: xs) = not (x `elem` xs) && allDistinct xs

||| the pattern solution: λ-abstract the ground over the applied
||| variables. An under-depth variable NOT among them would escape —
||| the match fails; spine-level variables strengthen by k and
||| weaken past the new binders.
absPat : (k : Nat) -> (vars : List Nat) -> Elem -> Maybe Elem
absPat k vars g = map (wrap (length vars)) (varMapE vf 0 g)
 where
  n : Nat
  n = length vars

  wrap : Nat -> Elem -> Elem
  wrap Z b = b
  wrap (S m) b = wrap m (PiIntro b)

  vf : (d : Nat) -> Nat -> Maybe Elem
  vf d m =
    if m < k
      then case lookup m (zip vars [0 .. minus n 1]) of
             Just j => Just (CtxVar (d + minus (minus n 1) j))
             Nothing => Nothing
      else Just (CtxVar (d + n + minus m k))

mutual
  ||| `applied` — the pattern sits in the function position of an
  ||| application: a hole here would be a flexible head, rejected by
  ||| the rigidity discipline. `k` — binders crossed since the spine:
  ||| a hole binding captured at depth k must STRENGTHEN by k (fail
  ||| if it mentions a crossed binder), so bindings stay
  ||| scope-correct at the spine.
  export
  mElemP : (pats : Bool) -> (applied : Bool) -> (k : Nat) -> (pat : Elem) -> (ground : Elem) -> Sols -> Maybe Sols
  mElemP pats app k (SigVar nm [<]) g sols =
    case holeView nm of
      Just i =>
        if app then Nothing else
          case strengthenE 0 k g of
            Nothing => Nothing
            Just g0 =>
              -- captures are COMP-NORMALIZED: a substituted domain
              -- can carry β-redexes ((λv. Int) w, from a
              -- pattern-solved dependency), and a redex core is not
              -- kernel-inferable — no surviving capture ever carried
              -- one, so normalizing is strictly additive
              let g' = compElem g0 in
              -- the bare-skeleton law, unconditionally: a hole
              -- solution ships with an empty skeleton, so an
              -- eliminator-bearing capture could never survive the
              -- kernel — refuse it here and let another source (or a
              -- spell-the-argument error) take the position
              if not (skelFreeE g') then Nothing else
              case lookup i sols of
                Just prev => if sameE prev g' then Just sols else Nothing
                Nothing => Just ((i, g') :: sols)
      Nothing => case g of
        SigVar nm' [<] => if nm == nm' then Just sols else Nothing
        _ => Nothing
  mElemP pats app k (SigVar nm sp) g sols =
    case g of
      SigVar nm' sp' => if nm == nm' then mSubP pats k sp sp' sols else Nothing
      _ => Nothing
  mElemP pats app k (CtxVar n) g sols =
    case g of CtxVar n' => if n == n' then Just sols else Nothing; _ => Nothing
  mElemP pats app k (ZeroElim t) g sols =
    case g of ZeroElim t' => mElemP pats False k t t' sols; _ => Nothing
  mElemP pats app k OneIntro g sols =
    case g of OneIntro => Just sols; _ => Nothing
  mElemP pats app k NatIntro0 g sols =
    case g of NatIntro0 => Just sols; _ => Nothing
  mElemP pats app k (NatIntro1 t) g sols =
    case g of NatIntro1 t' => mElemP pats False k t t' sols; _ => Nothing
  mElemP pats app k (NatElim z st t) g sols =
    case g of
      NatElim z' st' t' => mElemP pats False k z z' sols >>= mElemP pats False (k + 2) st st' >>= mElemP pats False k t t'
      _ => Nothing
  mElemP pats app k (PiIntro b) g sols =
    case g of PiIntro b' => mElemP pats False (S k) b b' sols; _ => Nothing
  mElemP pats app k (PiApp f a) g sols =
    case patView (PiApp f a) [] of
      -- the MILLER-PATTERN case: a hole applied to distinct bound
      -- variables (all under the spine's binders) matches ANY ground
      -- by abstraction — ?B x ↦ λx. ground — uniquely and without
      -- search. Non-pattern hole-headed spines still reject (the
      -- flexible-head discipline); rigid heads match structurally.
      Just (i, vars) =>
        if not pats then structural (PiApp f a) g sols else
        -- SKELETON-FREEDOM: the solution rides a bare skeleton, so a
        -- captured body containing stuck eliminators (their motives
        -- and coherences live in skeletons the kernel would need)
        -- must reject — same law as Phase 4's synthesized annotations
        if allDistinct vars && all (< k) vars && skelFreeE (compElem g)
          then case absPat k vars (compElem g) of
                 Nothing => Nothing
                 Just sol => case lookup i sols of
                   Just prev => if sameE prev sol then Just sols else Nothing
                   Nothing => Just ((i, sol) :: sols)
          else Nothing
      Nothing => structural (PiApp f a) g sols
   where
    structural : Elem -> Elem -> Sols -> Maybe Sols
    structural (PiApp pf pa) gg ss =
      case gg of
        PiApp f' a' => mElemP pats True k pf f' ss >>= mElemP pats False k pa a'
        _ => Nothing
    structural _ _ _ = Nothing
  mElemP pats app k (Let d b) g sols =
    case g of Let d' b' => mElemP pats False k d d' sols >>= mElemP pats False (k + 2) b b'; _ => Nothing
  mElemP pats app k (SigmaIntro u v) g sols =
    case g of SigmaIntro u' v' => mElemP pats False k u u' sols >>= mElemP pats False k v v'; _ => Nothing
  mElemP pats app k (SigmaElim1 t) g sols =
    case g of SigmaElim1 t' => mElemP pats False k t t' sols; _ => Nothing
  mElemP pats app k (SigmaElim2 t) g sols =
    case g of SigmaElim2 t' => mElemP pats False k t t' sols; _ => Nothing
  mElemP pats app k (Inj1 t) g sols =
    case g of Inj1 t' => mElemP pats False k t t' sols; _ => Nothing
  mElemP pats app k (Inj2 t) g sols =
    case g of Inj2 t' => mElemP pats False k t t' sols; _ => Nothing
  mElemP pats app k (SumElim l r t) g sols =
    case g of
      SumElim l' r' t' => mElemP pats False (S k) l l' sols >>= mElemP pats False (S k) r r' >>= mElemP pats False k t t'
      _ => Nothing
  mElemP pats app k ZeroTy g sols = case g of ZeroTy => Just sols; _ => Nothing
  mElemP pats app k OneTy g sols = case g of OneTy => Just sols; _ => Nothing
  mElemP pats app k NatTy g sols = case g of NatTy => Just sols; _ => Nothing
  mElemP pats app k UniverseTy g sols = case g of UniverseTy => Just sols; _ => Nothing
  mElemP pats app k PropTy g sols = case g of PropTy => Just sols; _ => Nothing
  mElemP pats app k TopTy g sols = case g of TopTy => Just sols; _ => Nothing
  mElemP pats app k (PiTy a b) g sols =
    case g of PiTy a' b' => mElemP pats False k a a' sols >>= mElemP pats False (S k) b b'; _ => Nothing
  mElemP pats app k (SigmaTy a b) g sols =
    case g of SigmaTy a' b' => mElemP pats False k a a' sols >>= mElemP pats False (S k) b b'; _ => Nothing
  mElemP pats app k (SumTy a b) g sols =
    case g of SumTy a' b' => mElemP pats False k a a' sols >>= mElemP pats False k b b'; _ => Nothing
  mElemP pats app k (EqTy l r ty) g sols =
    case g of
      EqTy l' r' ty' => mElemP pats False k l l' sols >>= mElemP pats False k r r' >>= mTyP pats k ty ty'
      _ => Nothing
  mElemP pats app k (QuotTy a r) g sols =
    case g of QuotTy a' r' => mElemP pats False k a a' sols >>= mElemP pats False (k + 2) r r'; _ => Nothing
  mElemP pats app k (Class t) g sols =
    case g of Class t' => mElemP pats False k t t' sols; _ => Nothing
  mElemP pats app k (QuotElim f q) g sols =
    case g of QuotElim f' q' => mElemP pats False (S k) f f' sols >>= mElemP pats False k q q'; _ => Nothing
  mElemP pats app k (Squash ty) g sols =
    case g of Squash ty' => mTyP pats k ty ty' sols; _ => Nothing
  mElemP pats app k Star g sols = case g of Star => Just sols; _ => Nothing
  mElemP pats app k (QSort sig j sp) g sols =
    case g of
      QSort sig' j' sp' =>
        if j == j' && show sig == show sig' then mSubP pats k sp sp' sols else Nothing
      _ => Nothing
  mElemP pats app k (QCtor sig j sp) g sols =
    case g of
      QCtor sig' j' sp' =>
        if j == j' && show sig == show sig' then mSubP pats k sp sp' sols else Nothing
      _ => Nothing
  mElemP pats app k (QElim sig j mots mths sp w) g sols =
    case g of
      QElim sig' j' mots' mths' sp' w' =>
        if j == j' && show sig == show sig'
          then mTys pats k mots mots' sols >>= mElems pats k mths mths' >>= mSubP pats k sp sp' >>= mElemP pats False k w w'
          else Nothing
      _ => Nothing
  mElemP pats app k (NuTy p) g sols =
    case g of NuTy p' => mPoly pats k p p' sols; _ => Nothing
  mElemP pats app k (Out t) g sols =
    case g of Out t' => mElemP pats False k t t' sols; _ => Nothing
  mElemP pats app k (Corec p a f x) g sols =
    case g of
      Corec p' a' f' x' =>
        mPoly pats k p p' sols >>= mElemP pats False k a a' >>= mElemP pats False (S k) f f' >>= mElemP pats False k x x'
      _ => Nothing

  mElems : (pats : Bool) -> (k : Nat) -> List Elem -> List Elem -> Sols -> Maybe Sols
  mElems pats k [] [] sols = Just sols
  mElems pats k (x :: xs) (y :: ys) sols = mElemP pats False k x y sols >>= mElems pats k xs ys
  mElems pats k _ _ _ = Nothing

  mTys : (pats : Bool) -> (k : Nat) -> List Ty -> List Ty -> Sols -> Maybe Sols
  mTys pats k [] [] sols = Just sols
  mTys pats k (x :: xs) (y :: ys) sols = mTyP pats k x y sols >>= mTys pats k xs ys
  mTys pats k _ _ _ = Nothing

  mSubP : (pats : Bool) -> (k : Nat) -> SubNorm -> SubNorm -> Sols -> Maybe Sols
  mSubP pats k [<] [<] sols = Just sols
  mSubP pats k (xs :< x) (ys :< y) sols = mSubP pats k xs ys sols >>= mElemP pats False k x y
  mSubP pats k _ _ _ = Nothing

  ||| The 𝕌-code of a type (El retired: for the shared formers the
  ||| code IS the type, so this is now the identity on them; large
  ||| formers have none).
  codeOfTy : Ty -> Maybe Elem
  codeOfTy UniverseTy = Nothing
  codeOfTy PropTy = Nothing
  codeOfTy TopTy = Nothing
  codeOfTy t = Just t

  export
  mTyP : (pats : Bool) -> (k : Nat) -> Ty -> Ty -> Sols -> Maybe Sols
  mTyP pats k ZeroTy g sols = case g of ZeroTy => Just sols; _ => Nothing
  mTyP pats k OneTy g sols = case g of OneTy => Just sols; _ => Nothing
  mTyP pats k NatTy g sols = case g of NatTy => Just sols; _ => Nothing
  mTyP pats k UniverseTy g sols = case g of UniverseTy => Just sols; _ => Nothing
  mTyP pats k PropTy g sols = case g of PropTy => Just sols; _ => Nothing
  mTyP pats k (PiTy a b) g sols =
    case g of PiTy a' b' => mTyP pats k a a' sols >>= mTyP pats (S k) b b'; _ => Nothing
  mTyP pats k (SigmaTy a b) g sols =
    case g of SigmaTy a' b' => mTyP pats k a a' sols >>= mTyP pats (S k) b b'; _ => Nothing
  mTyP pats k (SumTy a b) g sols =
    case g of SumTy a' b' => mTyP pats k a a' sols >>= mTyP pats k b b'; _ => Nothing
  mTyP pats k (QuotTy a r) g sols =
    case g of QuotTy a' r' => mTyP pats k a a' sols >>= mElemP pats False (k + 2) r r'; _ => Nothing
  -- SigVar in type position is a code pattern like any other — in
  -- particular a HOLE head must bind against a non-SigVar ground, so
  -- delegate to the elem matcher instead of demanding a SigVar ground
  mTyP pats k (SigVar nm sp) g sols =
    case codeOfTy g of
      Just c => mElemP pats False k (SigVar nm sp) c sols
      Nothing => Nothing
  mTyP pats k (QSort sig j sp) g sols =
    case g of
      QSort sig' j' sp' =>
        if j == j' && show sig == show sig' then mSubP pats k sp sp' sols else Nothing
      _ => Nothing
  mTyP pats k TopTy g sols = case g of TopTy => Just sols; _ => Nothing
  mTyP pats k (NuTy p) g sols = case g of NuTy p' => mPoly pats k p p' sols; _ => Nothing
  -- El retired: a non-former pattern in type position is a CODE
  -- pattern (possibly hole-headed) — match it against the ground as
  -- a code (untrusted; the kernel gate rejects ill-typed bindings)
  mTyP pats k t g sols = case codeOfTy g of
    Just c => mElemP pats False k t c sols
    Nothing => Nothing

  mPoly : (pats : Bool) -> (k : Nat) -> Poly -> Poly -> Sols -> Maybe Sols
  mPoly pats k PHole g sols = case g of PHole => Just sols; _ => Nothing
  mPoly pats k (PConst a) g sols = case g of PConst a' => mElemP pats False k a a' sols; _ => Nothing
  mPoly pats k (PProd f h) g sols =
    case g of PProd f' h' => mPoly pats k f f' sols >>= mPoly pats k h h'; _ => Nothing
  mPoly pats k (PSum f h) g sols =
    case g of PSum f' h' => mPoly pats k f f' sols >>= mPoly pats k h h'; _ => Nothing
  mPoly pats k (PSigma a f) g sols =
    case g of PSigma a' f' => mElemP pats False k a a' sols >>= mPoly pats (S k) f f'; _ => Nothing
  mPoly pats k (PPi a f) g sols =
    case g of PPi a' f' => mElemP pats False k a a' sols >>= mPoly pats (S k) f f'; _ => Nothing

||| The public match: the CLASSIC rigid engine. The MILLER-PATTERN
||| tier (mTyP True) is never part of the general path — the spine
||| elaborator invokes it explicitly, in an END-STAGE pass restricted
||| to holes the classic walk left unsolved, so every
||| previously-solving site solves identically.
export
mTy : (k : Nat) -> Ty -> Ty -> Sols -> Maybe Sols
mTy k pat g sols = mTyP False k pat g sols

export
mElem : (applied : Bool) -> (k : Nat) -> Elem -> Elem -> Sols -> Maybe Sols
mElem app k = mElemP False app k

-- ===== Telescopes =====

||| Peel the syntactic Π-telescope of a CLOSED Σ-type: the domains (as
||| written, each under its predecessors) and the residual type.
export
teleOf : Ty -> (List Ty, Ty)
teleOf (PiTy a b) = let (ds, r) = teleOf b in (a :: ds, r)
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
    UniverseTy => acc
    PropTy => acc
    TopTy => acc
    PiTy a b => walkE True a (walkE True b acc)
    SigmaTy a b => walkE True a (walkE True b acc)
    SumTy a b => walkE True a (walkE True b acc)
    EqTy l r ty => walkE True l (walkE True r (walkT ty acc))
    QuotTy a r => walkE True a (walkE True r acc)
    Class t => walkE True t acc
    QuotElim f q => walkE True f (walkE False q acc)
    Squash ty => walkT ty acc
    Star => acc
    QSort _ _ sp => foldl (\a, x => walkE True x a) acc (toList sp)
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
  walkT = walkE True

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

-- Does any Σ REFERENCE in the term satisfy `p`? One traversal, two
-- questions: the spine oracle asks whether its own placeholders
-- survive (`hasHolesE`), and the elaborator's hole refinement asks
-- whether a candidate solution mentions a given name — an occurs
-- check. Nothing else about the term is inspected, so the name test
-- is the whole of the difference.
mutual
  export
  anySigNameE : (String -> Bool) -> Elem -> Bool
  anySigNameE p e = case e of
    SigVar nm sp => p nm || any (anySigNameE p) (toList sp)
    CtxVar _ => False
    ZeroElim t => anySigNameE p t
    OneIntro => False
    NatIntro0 => False
    NatIntro1 t => anySigNameE p t
    NatElim z s t => anySigNameE p z || anySigNameE p s || anySigNameE p t
    PiIntro b => anySigNameE p b
    PiApp f a => anySigNameE p f || anySigNameE p a
    Let d b => anySigNameE p d || anySigNameE p b
    SigmaIntro u v => anySigNameE p u || anySigNameE p v
    SigmaElim1 t => anySigNameE p t
    SigmaElim2 t => anySigNameE p t
    Inj1 t => anySigNameE p t
    Inj2 t => anySigNameE p t
    SumElim l r t => anySigNameE p l || anySigNameE p r || anySigNameE p t
    ZeroTy => False
    OneTy => False
    NatTy => False
    UniverseTy => False
    PropTy => False
    TopTy => False
    Elem.PiTy a b => anySigNameE p a || anySigNameE p b
    Elem.SigmaTy a b => anySigNameE p a || anySigNameE p b
    Elem.SumTy a b => anySigNameE p a || anySigNameE p b
    Elem.EqTy l r t => anySigNameE p l || anySigNameE p r || anySigNameE p t
    QuotTy a r => anySigNameE p a || anySigNameE p r
    Class a => anySigNameE p a
    QuotElim f q => anySigNameE p f || anySigNameE p q
    Squash t => anySigNameE p t
    Star => False
    QSort _ _ sp => any (anySigNameE p) (toList sp)
    QCtor _ _ sp => any (anySigNameE p) (toList sp)
    QElim _ _ mots mths sp w =>
      any (anySigNameE p) mots || any (anySigNameE p) mths
        || any (anySigNameE p) (toList sp) || anySigNameE p w
    NuTy poly => anySigNameP p poly
    Out t => anySigNameE p t
    Corec poly a f x => anySigNameP p poly || anySigNameE p a || anySigNameE p f || anySigNameE p x

  export
  anySigNameP : (String -> Bool) -> Poly -> Bool
  anySigNameP p poly = case poly of
    PHole => False
    PConst a => anySigNameE p a
    PProd f g => anySigNameP p f || anySigNameP p g
    PSum f g => anySigNameP p f || anySigNameP p g
    PSigma a f => anySigNameE p a || anySigNameP p f
    PPi a f => anySigNameE p a || anySigNameP p f

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
    UniverseTy => False
    PropTy => False
    TopTy => False
    PiTy a b => hasHolesE a || hasHolesE b
    SigmaTy a b => hasHolesE a || hasHolesE b
    SumTy a b => hasHolesE a || hasHolesE b
    EqTy l r ty => hasHolesE l || hasHolesE r || hasHolesT ty
    QuotTy a r => hasHolesE a || hasHolesE r
    Class t => hasHolesE t
    QuotElim f q => hasHolesE f || hasHolesE q
    Squash ty => hasHolesT ty
    Star => False
    QSort _ _ sp => any hasHolesE (toList sp)
    QCtor _ _ sp => any hasHolesE (toList sp)
    QElim _ _ mots mths sp w =>
      any hasHolesT mots || any hasHolesE mths || any hasHolesE (toList sp) || hasHolesE w
    NuTy p => hasHolesP p
    Out t => hasHolesE t
    Corec p a f x => hasHolesP p || hasHolesE a || hasHolesE f || hasHolesE x

  ||| One sort (El retired): a type is an element, and a CODE type —
  ||| an application spine, say — carries holes exactly where the
  ||| element walk finds them. A former-only walk here would miss
  ||| `isZeroCode ?0` and let the spine walk check an argument at a
  ||| still-holey domain.
  export
  hasHolesT : Ty -> Bool
  hasHolesT = hasHolesE

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
rebuildTail (d :: ds) r = PiTy d (rebuildTail ds r)

-- ===== Scrutinee abstraction (motive recovery, Phase 4) =====
--
-- abs c scrut e: the body of the recovered motive — every occurrence
-- of the scrutinee (weakened by the local binder depth) becomes the
-- motive's bound variable, every other free variable shifts up by
-- one. Deterministic: replace-all, outermost-first. The recovered
-- motive for expected type C is `absT 0 scrut C` (one binder), and
-- instantiating it back at the scrutinee reproduces C exactly, so
-- the elided form's switch conversion is α-trivial.

wkN : Nat -> Sub
wkN Z = Id
wkN (S n) = Chain (wkN n) Wk

mutual
  export
  absE : (c : Nat) -> (scrut : Elem) -> Elem -> Elem
  absE c sc e =
    if show e == show (substElem sc (wkN c)) then CtxVar c else case e of
      CtxVar i => if i >= c then CtxVar (S i) else CtxVar i
      SigVar nm sp => SigVar nm (map (absE c sc) sp)
      ZeroElim t => ZeroElim (absE c sc t)
      OneIntro => e
      NatIntro0 => e
      NatIntro1 t => NatIntro1 (absE c sc t)
      NatElim z s t => NatElim (absE c sc z) (absE (c + 2) sc s) (absE c sc t)
      PiIntro b => PiIntro (absE (S c) sc b)
      PiApp f a => PiApp (absE c sc f) (absE c sc a)
      Let d b => Let (absE c sc d) (absE (c + 2) sc b)
      SigmaIntro u v => SigmaIntro (absE c sc u) (absE c sc v)
      SigmaElim1 t => SigmaElim1 (absE c sc t)
      SigmaElim2 t => SigmaElim2 (absE c sc t)
      Inj1 t => Inj1 (absE c sc t)
      Inj2 t => Inj2 (absE c sc t)
      SumElim l r t => SumElim (absE (S c) sc l) (absE (S c) sc r) (absE c sc t)
      ZeroTy => e
      OneTy => e
      NatTy => e
      UniverseTy => e
      PropTy => e
      TopTy => e
      PiTy a b => PiTy (absE c sc a) (absE (S c) sc b)
      SigmaTy a b => SigmaTy (absE c sc a) (absE (S c) sc b)
      SumTy a b => SumTy (absE c sc a) (absE c sc b)
      EqTy l r ty => EqTy (absE c sc l) (absE c sc r) (absT c sc ty)
      QuotTy a r => QuotTy (absE c sc a) (absE (c + 2) sc r)
      Class t => Class (absE c sc t)
      QuotElim f q => QuotElim (absE (S c) sc f) (absE c sc q)
      Squash ty => Squash (absT c sc ty)
      Star => e
      QSort sig k sp => QSort sig k (map (absE c sc) sp)
      QCtor sig k sp => QCtor sig k (map (absE c sc) sp)
      QElim sig k mots mths sp w =>
        QElim sig k (map (absT c sc) mots) (map (absE c sc) mths)
              (map (absE c sc) sp) (absE c sc w)
      NuTy p => NuTy (absP c sc p)
      Out t => Out (absE c sc t)
      Corec p a f x => Corec (absP c sc p) (absE c sc a) (absE (S c) sc f) (absE c sc x)

  ||| One sort (El retired): a type abstracts as its element spelling.
  ||| A former-only walk here would return a CODE type (an application
  ||| spine, a bound code) UNSHIFTED — silently capturing the new
  ||| binder — and would miss scrutinee occurrences inside it.
  export
  absT : (c : Nat) -> (scrut : Elem) -> Ty -> Ty
  absT = absE

  absP : (c : Nat) -> (scrut : Elem) -> Poly -> Poly
  absP c sc p = case p of
    PHole => p
    PConst a => PConst (absE c sc a)
    PProd f g => PProd (absP c sc f) (absP c sc g)
    PSum f g => PSum (absP c sc f) (absP c sc g)
    PSigma a f => PSigma (absE c sc a) (absP (S c) sc f)
    PPi a f => PPi (absE c sc a) (absP (S c) sc f)
