module Nova.Kernel.QIIT

-- Foundation's QIIT meta-operations (docs/NovaFoundation.txt, QIIT
-- section) as pure kernel functions: reflection ⌊·⌋ / ⌊·⌋ᵗ, the
-- ᴰ-translations (displayed telescope and method/coherence types), the
-- method image ⟦·⟧, and el-qiit-beta's section spine.
--
-- The WALK STATE realizes Foundation's (Γ̂, ρ, υ) accumulators, in
-- VALUE-passing style so one recursion covers both read-outs:
--   * type-building walks cross binders with fresh VARIABLES
--     (crossExtVar/crossIndVar — extSub is then the reindexer ρ);
--   * instantiating walks cross binders with the use-site spine's
--     VALUES (crossExtVal/crossIndVal — extSub is then the
--     instantiation of the external zone).
-- ToS variables (⬡ᵢ) resolve through ienv (inductive binders,
-- innermost first) and then into the signature's entries
-- (last-to-first); υ (ups) is the total weakening under which the
-- carried signature moves (𝒮[υ]).
--
-- FIRST-ORDER fragment: no external λ in ToS terms (infinitary
-- recursive arguments) and no equation-code Π domains; both are
-- rejected with explicit errors. Foundation covers them; nothing here
-- obstructs adding them later.

import Data.List
import Data.SnocList

import Nova.Kernel.Syntax
import Nova.Kernel.Subst

%default covering

public export
QErr : Type
QErr = String

public export
record QW where
  constructor MkQW
  extSub : Sub
  ienv : List Elem
  ups : Sub
  ||| ToS variables are relative to the ENTRY being walked: they see
  ||| its binders and then the signature's first `scope` entries (its
  ||| prefix), last-to-first.
  scope : Nat

export
qwAt : Nat -> QW
qwAt k = MkQW Id [] Id k

wkE : Elem -> Elem
wkE e = substElem e Wk

||| Cross an external binder, binding a fresh Nova variable.
export
crossExtVar : QW -> QW
crossExtVar (MkQW s env u k) = MkQW (under s) (map wkE env) (Chain u Wk) k

||| Cross an inductive binder, binding a fresh Nova variable.
export
crossIndVar : QW -> QW
crossIndVar (MkQW s env u k) = MkQW (Chain s Wk) (CtxVar 0 :: map wkE env) (Chain u Wk) k

||| Cross a Nova-only auxiliary binder (an IH slot of the ᴰ-context):
||| everything weakens, no ToS variable is bound.
export
crossAux : QW -> QW
crossAux (MkQW s env u k) = MkQW (Chain s Wk) (map wkE env) (Chain u Wk) k

||| Cross an external binder at a use-site VALUE.
export
crossExtVal : Elem -> QW -> QW
crossExtVal v (MkQW s env u k) = MkQW (Ext s v) env u k

||| Cross an inductive binder at a use-site VALUE.
export
crossIndVal : Elem -> QW -> QW
crossIndVal v (MkQW s env u k) = MkQW s (v :: env) u k

public export
data QVarRes = QVBinder Elem | QVEntry Nat

||| Resolve ⬡ᵢ: an inductive binder's value, or an entry position.
export
resolveQVar : QSig -> QW -> Nat -> Either QErr QVarRes
resolveQVar sg w i =
  let b = length w.ienv in
  if i < b
    then case getAt i w.ienv of
           Just v => Right (QVBinder v)
           Nothing => Left "qiit: internal — binder environment out of sync"
    else
      let j = minus i b in
      if j < w.scope
        then Right (QVEntry (minus (minus w.scope 1) j))
        else Left "qiit: ToS variable out of range"

mutual
  ||| Reflect a ToS element chain (a term of a sort) as a Nova element.
  export
  reflTm : QSig -> QW -> QTm -> Either QErr Elem
  reflTm sg w t = do
    (h, args) <- maybe (Left "qiit: not an application chain (first-order fragment)") Right (qChain t)
    r <- resolveQVar sg w h
    case r of
      QVBinder v =>
        case args of
          [] => Right v
          _ => Left "qiit: applied inductive binder (no higher-order binders in the first-order fragment)"
      QVEntry k => do
        entry <- maybe (Left "qiit: entry out of range") Right (qEntry sg k)
        case qEntryKind entry of
          QKPoint => do
            sp <- reflArgs sg w args
            Right (QCtor (substQSig sg w.ups) k sp)
          -- an EQUATION entry mints no term: its reflected ≡-type holds
          -- by el-qiit-path, and ⋆ inhabits its Prf (el-eq-i)
          QKEq => Right Star
          QKSort => Left "qiit: a sort is a type former, not a term"

  ||| Reflect a chain's argument list as a Nova spine (external args
  ||| through the external-zone substitution, inductive args recursively).
  export
  reflArgs : QSig -> QW -> List (Either Elem QTm) -> Either QErr SubNorm
  reflArgs sg w args =
    foldlM (\acc, a => case a of
             Left e => Right (acc :< substElem e w.extSub)
             Right t => (acc :<) <$> reflTm sg w t) [<] args

  ||| Reflect a CODE as the Nova TYPE it decodes to: a sort-headed chain
  ||| becomes the sort former, an equation code an ≡-type.
  export
  reflCodeTy : QSig -> QW -> QTm -> Either QErr Ty
  reflCodeTy sg w (QEqC l r u) = do
    l' <- reflTm sg w l
    r' <- reflTm sg w r
    u' <- reflCodeTy sg w u
    Right (Prf (Elem.EqTy l' r' u'))
  reflCodeTy sg w t = do
    (s, args) <- codeSort sg w t
    sp <- reflArgs sg w args
    Right (QSort (substQSig sg w.ups) s sp)

  ||| Reflect a CODE as a universe code (element of 𝕌) — the sort code
  ||| former (small signatures; smallness is the caller's premise).
  export
  reflCode : QSig -> QW -> QTm -> Either QErr Elem
  reflCode sg w (QEqC l r u) =
    -- equality is Ω-valued: there is no 𝕌-code for it (and
    -- equation-code binders are outside the checked fragment, A6)
    Left "equation code in a 𝕌-code position (equality is Ω-valued)"
  reflCode sg w t = do
    (s, args) <- codeSort sg w t
    sp <- reflArgs sg w args
    Right (QSortC (substQSig sg w.ups) s sp)

  ||| A sort-headed code's sort position and argument chain.
  export
  codeSort : QSig -> QW -> QTm -> Either QErr (Nat, List (Either Elem QTm))
  codeSort sg w t = do
    (h, args) <- maybe (Left "qiit: code is not a sort application") Right (qChain t)
    r <- resolveQVar sg w h
    case r of
      QVEntry k => do
        entry <- maybe (Left "qiit: entry out of range") Right (qEntry sg k)
        case qEntryKind entry of
          QKSort => Right (k, args)
          _ => Left "qiit: code head is not a sort"
      QVBinder _ => Left "qiit: code head is a binder, not a sort"

||| ⌊𝔄⌋ — an El-ended type as a Nova Π-type (variable walk).
export
reflQTy : QSig -> QW -> QTy -> Either QErr Ty
reflQTy sg w (QEl code) = reflCodeTy sg w code
reflQTy sg w (QPiExt a b) = Ty.PiTy (substTy a w.extSub) <$> reflQTy sg (crossExtVar w) b
reflQTy sg w (QPiInd u b) = do
  d <- reflCodeTy sg w u
  Ty.PiTy d <$> reflQTy sg (crossIndVar w) b
reflQTy sg w QU = Left "qiit: U-ended type where an El-ended one is expected"

||| ⌊·⌋ᵗ — the binder (or arity) telescope: entries outermost first,
||| entry i in the context of the previous binders; plus the final walk
||| state and the head.
export
reflTel : QSig -> QW -> QTy -> Either QErr (List Ty, QW, QTy)
reflTel sg w (QPiExt a b) = do
  (tel, wEnd, hd) <- reflTel sg (crossExtVar w) b
  Right (substTy a w.extSub :: tel, wEnd, hd)
reflTel sg w (QPiInd u b) = do
  d <- reflCodeTy sg w u
  (tel, wEnd, hd) <- reflTel sg (crossIndVar w) b
  Right (d :: tel, wEnd, hd)
reflTel sg w hd = Right ([], w, hd)

||| Walk a type's binders at a use-site VALUE spine, classifying each
||| value by its binder's kind; returns the final state and the head.
export
walkVals : QSig -> QW -> QTy -> List Elem -> Either QErr (QW, QTy)
walkVals sg w (QPiExt _ b) (v :: vs) = walkVals sg (crossExtVal v w) b vs
walkVals sg w (QPiInd _ b) (v :: vs) = walkVals sg (crossIndVal v w) b vs
walkVals sg w (QPiExt _ _) [] = Left "qiit: unsaturated constructor spine"
walkVals sg w (QPiInd _ _) [] = Left "qiit: unsaturated constructor spine"
walkVals sg w hd [] = Right (w, hd)
walkVals sg w _ _ = Left "qiit: constructor spine too long"

||| A point constructor's result: its sort position and the reflected
||| index spine, at the given (end-of-walk) state.
export
pointHead : QSig -> QW -> QTy -> Either QErr (Nat, SubNorm)
pointHead sg w (QEl code) = do
  (s, args) <- codeSort sg w code
  sp <- reflArgs sg w args
  Right (s, sp)
pointHead sg w _ = Left "qiit: not a point-constructor head"

||| An equation constructor's head: the two sides and their common code.
export
eqHead : QTy -> Either QErr (QTm, QTm, QTm)
eqHead (QEl (QEqC l r u)) = Right (l, r, u)
eqHead _ = Left "qiit: not an equation-constructor head"

||| The variable spine δ of a telescope with n entries (outermost binder
||| first): ☐_{n-1}, …, ☐₀.
export
varSpine : Nat -> SubNorm
varSpine n = cast (map CtxVar (go n))
 where
  go : Nat -> List Nat
  go Z = []
  go (S m) = m :: go m

||| Instantiate telescope entry i (over Γ + i binders) at the earlier
||| arguments (over Γ).
export
telInst : List Ty -> Nat -> List Elem -> Maybe Ty
telInst tel i args = do
  ty <- getAt i tel
  pure (substTy ty (foldl Ext Id (take i args)))

-- ===== Motive application =====

||| C_s[ē, w] — the motive for sort s (a type over Γ·⌊𝔎⌋ᵗ ▷ 𝒮.s δ)
||| instantiated at an index spine and eliminee, with `base` the
||| substitution from the current context back to Γ (υ of the walk).
export
motApp : QSig -> List Ty -> Sub -> Nat -> SubNorm -> Elem -> Either QErr Ty
motApp sg mots base s idx self = do
  o <- maybe (Left "qiit: not a sort position") Right (qOrdinal QKSort sg s)
  m <- maybe (Left "qiit: motive missing") Right (getAt o mots)
  Right (substTy m (Ext (foldl Ext base (toList idx)) self))

-- ===== el-qiit-beta =====

||| The β right-hand side: the ctor's method applied to the section
||| spine at φᵉˡ — each inductive argument contributes its value AND a
||| recursive eliminator call at its own sort and indices.
export
qElimBetaRhs : QSig -> (motives : List Ty) -> (methods : List Elem)
            -> (ctorPos : Nat) -> (theta : SubNorm) -> Either QErr Elem
qElimBetaRhs sg mots mths k theta = do
  entry <- maybe (Left "qiit: ctor out of range") Right (qEntry sg k)
  o <- maybe (Left "qiit: not a point-constructor position") Right (qOrdinal QKPoint sg k)
  m <- maybe (Left "qiit: method missing") Right (getAt o mths)
  go m (qwAt k) entry (toList theta)
 where
  go : Elem -> QW -> QTy -> List Elem -> Either QErr Elem
  go acc w (QPiExt _ b) (v :: vs) = go (PiApp acc v) (crossExtVal v w) b vs
  go acc w (QPiInd u b) (v :: vs) = do
    (s, args) <- codeSort sg w u
    idx <- reflArgs sg w args
    let rec = QElim sg s mots mths idx v
    go (PiApp (PiApp acc v) rec) (crossIndVal v w) b vs
  go acc _ (QEl _) [] = Right acc
  go _ _ _ _ = Left "qiit: β constructor spine mismatch"

-- ===== The ᴰ-walk (displayed telescope) =====

||| State of a ᴰ-walk over a constructor's binders, with VARIABLES:
||| the displayed telescope so far, the walk state (which folds πᴰ in —
||| its indices are ᴰ-context indices), the IH value of each inductive
||| binder (parallel to ienv), and the accumulated argument-variable
||| spine (for saturating the constructor / candidate section).
public export
record DW where
  constructor MkDW
  dtel : SnocList Ty
  w : QW
  dihs : List (Maybe Elem)
  spine : SubNorm

export
dwAt : Nat -> DW
dwAt k = MkDW [<] (qwAt k) [] [<]

||| Walk a constructor type's binders in ᴰ-mode: an external binder
||| contributes its argument; an inductive binder its argument AND its
||| induction hypothesis (equation-code domains are rejected — the
||| first-order fragment).
export
dispWalk : QSig -> List Ty -> (entryPos : Nat) -> QTy -> Either QErr (DW, QTy)
dispWalk sg mots pos ty0 = go (dwAt pos) ty0
 where
  wkAll : DW -> DW
  wkAll (MkDW dtel w dihs sp) =
    MkDW dtel w (map (map wkE) dihs) (substSubNorm sp Wk)
  go : DW -> QTy -> Either QErr (DW, QTy)
  go dw (QPiExt a b) = do
    let entry = substTy a dw.w.extSub
    let dw1 = wkAll ({ w $= crossExtVar } dw)
    let dw2 = { dtel $= (:< entry), spine $= (:< CtxVar 0) } dw1
    go dw2 b
  go dw (QPiInd u b) = do
    case u of
      QEqC _ _ _ => Left "qiit: equation-code binder (first-order fragment)"
      _ => pure ()
    valEntry <- reflCodeTy sg dw.w u
    -- cross the VALUE binder
    let dw1 = wkAll ({ w $= crossIndVar, dihs $= (Nothing ::) } dw)
    let dw2 = { dtel $= (:< valEntry), spine $= (:< CtxVar 0) } dw1
    -- the IH entry: C_s[⌊ī⌋, ☐₀] at the just-bound value. u was written
    -- BEFORE the value binder, so its ToS references shift past it.
    let u' = qtmShift 1 u
    (s, args) <- codeSort sg dw2.w u'
    idx <- reflArgs sg dw2.w args
    ihEntry <- motApp sg mots dw2.w.ups s idx (CtxVar 0)
    -- cross the IH binder (Nova-only)
    let dw3 = wkAll ({ w $= crossAux } dw2)
    let dw4 = { dtel $= (:< ihEntry), dihs $= setIH } dw3
    go dw4 b
   where
    setIH : List (Maybe Elem) -> List (Maybe Elem)
    setIH [] = []
    setIH (_ :: rest) = Just (CtxVar 0) :: rest
  go dw hd = Right (dw, hd)

||| The METHOD TYPE for point constructor k: 𝔄ᴰ⟨𝒮.k δ⟩ — the Π over the
||| displayed telescope ending in the motive at the saturated
||| constructor.
export
methodTy : QSig -> List Ty -> Nat -> Either QErr Ty
methodTy sg mots k = do
  entry <- maybe (Left "qiit: ctor out of range") Right (qEntry sg k)
  (dw, hd) <- dispWalk sg mots k entry
  (s, idx) <- pointHead sg dw.w hd
  cod <- motApp sg mots dw.w.ups s idx (QCtor (substQSig sg dw.w.ups) k dw.spine)
  Right (foldr Ty.PiTy cod (toList dw.dtel))

-- ===== Method image (coherences) =====

||| ⟦𝕥⟧ — the image of a qiit-term under the methods, in the ᴰ-context
||| of an equation entry's walk: a variable maps to its induction
||| hypothesis, a constructor chain to its method applied to values
||| interleaved with images.
export
mimg : QSig -> List Ty -> List Elem -> DW -> QTm -> Either QErr Elem
mimg sg mots mths dw t = do
  (h, args) <- maybe (Left "qiit: not an application chain") Right (qChain t)
  r <- resolveQVar sg dw.w h
  case r of
    QVBinder _ =>
      case (args, getAt h dw.dihs) of
        ([], Just (Just ih)) => Right ih
        ([], _) => Left "qiit: variable without an induction hypothesis in a method image"
        _ => Left "qiit: applied binder in a method image (first-order fragment)"
    QVEntry k => do
      entry <- maybe (Left "qiit: entry out of range") Right (qEntry sg k)
      case qEntryKind entry of
        QKPoint => do
          o <- maybe (Left "qiit: not a point position") Right (qOrdinal QKPoint sg k)
          m <- maybe (Left "qiit: method missing") Right (getAt o mths)
          foldlM app (substElem m dw.w.ups) args
        _ => Left "qiit: method image of a non-point head"
 where
  app : Elem -> Either Elem QTm -> Either QErr Elem
  app acc (Left e) = Right (PiApp acc (substElem e dw.w.extSub))
  app acc (Right t') = do
    v <- reflTm sg dw.w t'
    img <- mimg sg mots mths dw t'
    Right (PiApp (PiApp acc v) img)

||| The COHERENCE demanded of an elimination problem at equation entry
||| k: (ᴰ-context extension, the ARGUMENT-slot spine — the equation's
||| own binder values within that context — lhs image, rhs image,
||| their type).
export
coherenceAt : QSig -> List Ty -> List Elem -> Nat
           -> Either QErr (List Ty, SubNorm, Elem, Elem, Ty)
coherenceAt sg mots mths k = do
  entry <- maybe (Left "qiit: entry out of range") Right (qEntry sg k)
  (dw, hd) <- dispWalk sg mots k entry
  (l, r, u) <- eqHead hd
  (s, args) <- codeSort sg dw.w u
  idx <- reflArgs sg dw.w args
  lhs <- mimg sg mots mths dw l
  rhs <- mimg sg mots mths dw r
  lRefl <- reflTm sg dw.w l
  ty <- motApp sg mots dw.w.ups s idx lRefl
  Right (toList dw.dtel, dw.spine, lhs, rhs, ty)
