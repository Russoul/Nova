module Nova.Elaboration.Cert

-- The discharge ENGINE's certificate language, and its translation into
-- the kernel's proof terms (Nova.Kernel.Prf).
--
-- The engine finds equations by rewriting: it records what it did as a
-- list of STEPS (a licence applied at a path in one side), a type
-- bridge and a final. Nothing here is trusted. At the boundary to the
-- kernel a certificate is TRANSLATED into a proof term — the congruence
-- skeleton around each licence, transitivity between the rewritten
-- forms, the type-directed final as a leaf — by replaying its steps
-- engine-side (the same β join, the same licence reading, so the
-- proof's skeletons are over the terms the kernel will decompose). The
-- kernel then checks the proof term and nothing else: paths, steps and
-- finals never reach it.

import Data.List
import Data.Maybe
import Data.SnocList
import Control.Monad.State

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel.QIIT
import Nova.Kernel

%default covering

||| The ENGINE's selectors: as the kernel's (Nova.Kernel.Sel) but with
||| the instantiation ELEMENTS a match binds; the translation states
||| each as a proof at the domain the licence's sides show.
public export
data ESel : Type where
  ESelSuc : ESel
  ESelDom : ESel
  ESelCod : Elem -> ESel
  ESelSumL : ESel
  ESelSumR : ESel
  ESelQDom : ESel
  ESelQRel : Elem -> Elem -> ESel
  ESelQIdx : Nat -> ESel

export
covering
Show ESel where
  show ESelSuc = "suc"
  show ESelDom = "dom"
  show (ESelCod u) = "cod(\{show u})"
  show ESelSumL = "inl"
  show ESelSumR = "inr"
  show ESelQDom = "qdom"
  show (ESelQRel u v) = "qrel(\{show u},\{show v})"
  show (ESelQIdx i) = "idx\{show i}"

||| A step's LICENSE: a proof element whose type exposes an ≡-type
||| (equality reflection read certificate-side), or a PATH LICENSE —
||| an imposed equation of a QIIT signature (el-qiit-path): entry
||| position plus the full argument spine.
public export
data StepLic : Type where
  LProof : Elem -> StepLic
  LPath : QSig -> Nat -> SubNorm -> StepLic
  ||| A δ LICENSE — the ONLY way a definition unfolds during replay.
  ||| FORWARD (flip = False) it replaces the occurrence x[ē] at the
  ||| path — matched literally, spine compared modulo β — by t[ē]; the
  ||| spine is spelled AT the occurrence (it may mention binders the
  ||| path crossed). FLIPPED it REFOLDS t[ē] into x[ē] through the
  ||| ordinary licence path (the spine in the root context).
  LUnfold : String -> SubNorm -> StepLic
  ||| Every addressable occurrence of the named definitions unfolds AT
  ||| ONCE (forward only, path []): the δ-round of a join.
  LUnfoldAll : List String -> StepLic

||| One rewrite step: at `path` (child indices; binders crossed are
||| counted by the walk itself) in the chosen side, rewrite by the
||| licensed equation, after applying `sels` and possibly flipping.
||| Licences are spelled in the ROOT context of the equation.
public export
record Step where
  constructor MkStep
  onLhs : Bool
  path : List Nat
  lic : StepLic
  sels : List ESel
  flip : Bool
  ||| Steps NORMALIZING the licensed equation's OWN sides before it is
  ||| used (onLhs selects the licence's lhs or rhs): applied to the
  ||| licence's β-joined sides, at the licence's type in the root
  ||| context. This is how a licence stated in one spelling applies at
  ||| a position spelled otherwise.
  licNorm : List Step

mutual
  public export
  data Final : Type where
    ||| compare beta-normal forms
    FBeta : Final
    ||| the equation's type normalizes to 𝟙 or 𝟘 or to a PROPOSITION
    FProp : Final
    ||| class a ≐ class b at A / R via the relation's shape
    FWitness : Maybe ECert -> Final
    ||| el-quot-eq with the witness SUPPLIED
    FWitnessPrf : Elem -> Skel -> Final
    ||| same-tag injections at A ⊎ B are equal when their payloads are
    FInj : ECert -> Final
    ||| el-pi-eta: compare applied to the fresh variable, under the domain
    FEtaPi : ECert -> Final
    ||| el-sigma-eta: compare the projections
    FEtaSigma : ECert -> ECert -> Final
    ||| code-prop-eq (propositional extensionality) at Ω: the two
    ||| implications as FUNCTIONS over Γ, with their checking skeletons
    FPropExt : Elem -> Skel -> Elem -> Skel -> Final
    ||| prop-lift-eq for a TYPE certificate
    FPrfCong : ECert -> Final
    ||| ty-quot-cong (reflexive domain) for a TYPE certificate
    FQuotCong : ECert -> Final
    ||| ty-pi-cong for a TYPE certificate: domain certificate, then
    ||| codomain certificate under the (right) domain
    FPiCong : ECert -> ECert -> Final
    ||| ty-sigma-cong, same shape
    FSigmaCong : ECert -> ECert -> Final
    ||| ty-sum-cong, componentwise
    FSumCong : ECert -> ECert -> Final
    ||| TRANSITIVITY through STATED middles (el-trans): the points
    ||| p₀ … pₙ, each with its skeleton, and n + 2 certificates —
    ||| l ≐ p₀, then pᵢ₋₁ ≐ pᵢ for each link, then pₙ ≐ r
    FChain : List (Elem, Skel) -> List ECert -> Final

  public export
  record ECert where
    constructor MkECertF
    ||| Type bridge: replay the equation at tyX instead of the site's
    ||| type, justified by a TYPE certificate for  site-ty ≐ tyX
    tyEx : Maybe (Ty, ECert)
    steps : List Step
    final : Final

public export
MkECert : List Step -> Final -> ECert
MkECert steps final = MkECertF Nothing steps final

-- Diagnostics only: a certificate's shape (skeletons elided).
export
covering
Show StepLic where
  show (LProof p) = "proof \{show p}"
  show (LPath _ k th) = "path \{show k} \{show th}"
  show (LUnfold x es) = "unfold \{x} \{show es}"
  show (LUnfoldAll ns) = "unfold-all \{show ns}"

mutual
  export
  covering
  Show Step where
    show st = "{\{if st.onLhs then "L" else "R"} @\{show st.path} \{show st.lic}\{if null st.sels then "" else " sels=" ++ show st.sels}\{if st.flip then " flipped" else ""}\{if null st.licNorm then "" else " licNorm=" ++ show st.licNorm}}"

  export
  covering
  Show Final where
    show FBeta = "β"
    show FProp = "prop"
    show (FWitness c) = "witness \{show c}"
    show (FWitnessPrf w _) = "witness-prf \{show w}"
    show (FInj c) = "inj \{show c}"
    show (FEtaPi c) = "η→ \{show c}"
    show (FEtaSigma c1 c2) = "η× \{show c1} \{show c2}"
    show (FPropExt f _ g _) = "propext \{show f} \{show g}"
    show (FPrfCong c) = "prf-cong \{show c}"
    show (FQuotCong c) = "quot-cong \{show c}"
    show (FPiCong c1 c2) = "Π-cong \{show c1} \{show c2}"
    show (FSigmaCong c1 c2) = "Σ-cong \{show c1} \{show c2}"
    show (FSumCong c1 c2) = "⊎-cong \{show c1} \{show c2}"
    show (FChain pts cs) = "chain \{show (map fst pts)} \{show cs}"

  export
  covering
  Show ECert where
    show (MkECertF tyEx steps final) =
      let bridge = the String (case tyEx of
                     Nothing => ""
                     Just (t, c) => "bridge " ++ show t ++ " by " ++ show c ++ "; ") in
      "cert(" ++ bridge ++ "steps=" ++ show steps ++ "; final=" ++ show final ++ ")"

-- ===== Translation into proof terms =====

||| Wk composed n times (the weakening Γ·(n entries) ⇒ Γ).
wkN : Nat -> Sub
wkN Z = Id
wkN (S n) = Chain (wkN n) Wk

listAt : Nat -> List a -> Maybe a
listAt Z (x :: _) = Just x
listAt (S n) (_ :: xs) = listAt n xs
listAt _ [] = Nothing

listSet : Nat -> a -> List a -> Maybe (List a)
listSet Z y (_ :: xs) = Just (y :: xs)
listSet (S n) y (x :: xs) = map (x ::) (listSet n y xs)
listSet _ _ [] = Nothing

||| A spine with one child rewritten: the proofs (reflexivity at every
||| other entry) and the new spine.
spineWrap : Nat -> SubNorm -> (Elem -> KM (Prf, Elem)) -> KM (List Prf, SubNorm)
spineWrap i es go = do
  let xs = toList es
  e <- case listAt i xs of
         Just e => pure e
         Nothing => kerr "certificate: bad path (spine index)"
  (q, e') <- go e
  xs' <- case listSet i e' xs of
           Just v => pure v
           Nothing => kerr "certificate: bad path (spine index)"
  pure (map (\j => if j == i then q else PReflx) (indices xs), cast xs')
 where
  indices : List a -> List Nat
  indices ys = go' 0 ys
   where
    go' : Nat -> List a -> List Nat
    go' _ [] = []
    go' k (_ :: rest) = k :: go' (S k) rest

||| A congruence node around a child proof that is reflexivity is
||| reflexivity.
congOf : Prf -> Prf -> Prf
congOf PReflx _ = PReflx
congOf _ node = node

||| Wrap a proof at a position whose type was exposed by δ in the
||| conversion to the exposed spelling.
convWrap : Prf -> Ty -> Prf -> Prf
convWrap PReflx _ p = p
convWrap pt tyX p = PConv pt tyX p

||| The kernel's β-only type agreement (join, or cumulativity).
tyAgreeB : Sig -> Ty -> Ty -> KM Bool
tyAgreeB sig a b = do
  aN <- kJoinTy sig a
  bN <- kJoinTy sig b
  pure (aN == bN || (aN == TopTy && bN == UniverseTy))

||| Definition names occurring in a term.
||| The embedded Nova pieces of a carried signature.
export
piecesOf : QSig -> List Elem
piecesOf g = fst (runState [] (traverseQSig (\e => do modify (e ::); pure e) g))

defNames : Sig -> Elem -> KM (List String)
defNames sig t = do
  ns <- traverse isDef (nub (names t []))
  pure (catMaybes ns)
 where
  isDef : String -> KM (Maybe String)
  isDef x = kSigLookup sig x >>= \e => pure (case e of
                                               Just (SigDef _ _ _ _) => Just x
                                               _ => Nothing)
  names : Elem -> List String -> List String
  names (SigVar x es) acc = foldl (\a, e => names e a) (x :: acc) (toList es)
  names (ZeroElim u) acc = names u acc
  names (NatIntro1 u) acc = names u acc
  names (NatElim z st u) acc = names z (names st (names u acc))
  names (PiIntro f) acc = names f acc
  names (PiApp f e) acc = names f (names e acc)
  names (Let a b) acc = names a (names b acc)
  names (SigmaIntro u v) acc = names u (names v acc)
  names (SigmaElim1 u) acc = names u acc
  names (SigmaElim2 u) acc = names u acc
  names (Inj1 u) acc = names u acc
  names (Inj2 u) acc = names u acc
  names (SumElim l r u) acc = names l (names r (names u acc))
  names (Elem.PiTy a c) acc = names a (names c acc)
  names (Elem.SigmaTy a c) acc = names a (names c acc)
  names (Elem.SumTy a c) acc = names a (names c acc)
  names (Elem.EqTy l r u) acc = names l (names r (names u acc))
  names (QuotTy a r) acc = names a (names r acc)
  names (Class a) acc = names a acc
  names (QuotElim f q) acc = names f (names q acc)
  names (Squash u) acc = names u acc
  names (QSort sg _ es) acc = foldl (\a, e => names e a) acc (piecesOf sg ++ toList es)
  names (QCtor sg _ es) acc = foldl (\a, e => names e a) acc (piecesOf sg ++ toList es)
  names (QElim sg _ _ es w) acc = foldl (\a, e => names e a) (names w acc) (piecesOf sg ++ toList es)
  names (Out u) acc = names u acc
  names (Corec _ a f x) acc = names a (names f (names x acc))
  names _ acc = acc

||| A proof of a ≐ b (at 𝕍, or any type) by δ-rounds on both sides:
||| every definition occurring unfolds at once, the sides β-join,
||| repeat while new names appear — the engine's widening δβ join as
||| a proof. Nothing when the sides never meet.
deltaPrf : Sig -> Elem -> Elem -> KM (Maybe Prf)
deltaPrf sig a0 b0 = do
  aJ <- kJoinElem sig a0
  bJ <- kJoinElem sig b0
  go 64 [] aJ bJ [] []
 where
  chain : List Prf -> Prf
  chain [] = PReflx
  chain (p :: ps) = PTrans p (chain ps)
  -- every definition occurring on either side unfolds each round (a
  -- body may bring back a name an earlier round unfolded); stop at a
  -- fixed point
  go : Nat -> List String -> Elem -> Elem -> List Prf -> List Prf -> KM (Maybe Prf)
  go k seen a b la lb =
    if a == b then pure (Just (pTrans (chain (reverse la)) (pSym (chain (reverse lb)))))
    else case k of
      Z => pure Nothing
      S k' => do
        na <- defNames sig a
        nb <- defNames sig b
        let ns = nub (na ++ nb)
        case ns of
          [] => pure Nothing
          _ => do
            a' <- unfoldAllK sig ns a >>= kJoinElem sig
            b' <- unfoldAllK sig ns b >>= kJoinElem sig
            if a' == a && b' == b then pure Nothing
              else go k' (seen ++ ns) a' b' (PDeltaAll ns :: la) (PDeltaAll ns :: lb)

||| Is the term a SPINE — typable from its head's declared type by
||| eliminations alone (self leaves and elimination nodes)?
isSpine : Elem -> Bool
isSpine (CtxVar _) = True
isSpine (SigVar _ _) = True
isSpine (PiApp f _) = isSpine f
isSpine (SigmaElim1 t) = isSpine t
isSpine (SigmaElim2 t) = isSpine t
isSpine (Out t) = isSpine t
isSpine NatIntro0 = True
isSpine OneIntro = True
isSpine Elem.ZeroTy = True
isSpine Elem.OneTy = True
isSpine Elem.NatTy = True
isSpine _ = False

mutual
  ||| Head exposure with its δ RECORDED: the term taken to its β-whnf
  ||| with every definition unfolded on the way to the head as a δ leaf
  ||| inside the congruence skeleton of its position — and the proof of
  ||| t ≐ exposed (reflexivity when β alone reached it, which the
  ||| kernel's own whnf does).
  exposeK : Sig -> Ctx -> Elem -> KM (Elem, Prf)
  exposeK sig ctx t = go t
   where
    go : Elem -> KM (Elem, Prf)
    go (SigVar x es) =
      kSigLookup sig x >>= \entryX => case entryX of
        Just (SigDef _ _ a _) => do
          qs <- deltaArgs sig ctx x es
          (r, p) <- go (substElem a (embed es))
          pure (r, pTrans (PDelta x qs) p)
        _ => pure (SigVar x es, PReflx)
    go (PiApp f e) = do
      (f', p1) <- go f
      case f' of
        PiIntro g => do
          (r, p2) <- go (substElem g (Ext Id e))
          pure (r, pTrans (congOf p1 (CPiApp p1 PReflx)) p2)
        _ => pure (PiApp f' e, congOf p1 (CPiApp p1 PReflx))
    go (Let a b) = go (substElem b (Ext (Ext Id a) Star))
    go (NatElim z s t) = do
      (t', p1) <- go t
      let node = congOf p1 (CNatElim Nothing PReflx PReflx p1)
      case t' of
        NatIntro0 => do (r, p2) <- go z; pure (r, pTrans node p2)
        NatIntro1 n => do (r, p2) <- go (substElem s (Ext (Ext Id n) (NatElim z s n))); pure (r, pTrans node p2)
        _ => pure (NatElim z s t', node)
    go (SigmaElim1 t) = do
      (t', p1) <- go t
      case t' of
        SigmaIntro a _ => do (r, p2) <- go a; pure (r, pTrans (congOf p1 (CSigmaElim1 p1)) p2)
        _ => pure (SigmaElim1 t', congOf p1 (CSigmaElim1 p1))
    go (SigmaElim2 t) = do
      (t', p1) <- go t
      case t' of
        SigmaIntro _ b => do (r, p2) <- go b; pure (r, pTrans (congOf p1 (CSigmaElim2 p1)) p2)
        _ => pure (SigmaElim2 t', congOf p1 (CSigmaElim2 p1))
    go (SumElim l r t) = do
      (t', p1) <- go t
      let node = congOf p1 (CSumElim Nothing PReflx PReflx p1)
      case t' of
        Inj1 a => do (r', p2) <- go (substElem l (Ext Id a)); pure (r', pTrans node p2)
        Inj2 b => do (r', p2) <- go (substElem r (Ext Id b)); pure (r', pTrans node p2)
        _ => pure (SumElim l r t', node)
    go (QuotElim f q) = do
      (q', p1) <- go q
      case q' of
        Class a => do (r, p2) <- go (substElem f (Ext Id a)); pure (r, pTrans (congOf p1 (CQuotElim Nothing PReflx p1)) p2)
        _ => pure (QuotElim f q', congOf p1 (CQuotElim Nothing PReflx p1))
    go (Out t) = do
      (t', p1) <- go t
      case t' of
        Corec p a f x => do
          (r, p2) <- go (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
          pure (r, pTrans (congOf p1 (COut p1)) p2)
        _ => pure (Out t', congOf p1 (COut p1))
    go (QElim sg k fs es w) = do
      (w', p1) <- go w
      let node = congOf p1 (CQElim sg k Nothing (map (const PReflx) fs) (map (const PReflx) (toList es)) p1)
      case w' of
        QCtor sgW c theta =>
          if sgW == sg
            then case qElimBetaRhs sg fs c theta of
                   Right rhs => do (r, p2) <- go rhs; pure (r, pTrans node p2)
                   Left _ => pure (QElim sg k fs es w', node)
            else pure (QElim sg k fs es w', node)
        _ => pure (QElim sg k fs es w', node)
    -- the squashee exposed inside its ∥·∥; a squashee that exposes to a
    -- prop collapses (code-squash-idem's instance, a β-rule of the join)
    go (Squash t) = do
      (t', p1) <- go t
      let node = congOf p1 (CSquash p1)
      pure (case t' of
              Elem.EqTy _ _ _ => (t', node)
              Squash _ => (t', node)
              _ => (Squash t', node))
    go e = pure (e, PReflx)

  ||| Expose a position's type, when known.
  exposeMaybe : Sig -> Ctx -> Maybe Ty -> KM (Maybe (Ty, Prf))
  exposeMaybe sig ctx Nothing = pure Nothing
  exposeMaybe sig ctx (Just t) = Just <$> exposeK sig ctx t

  ||| The spine of a δ leaf stated entrywise: proof i at Δ's entry type
  ||| instantiated by the earlier entries.
  deltaArgs : Sig -> Ctx -> String -> SubNorm -> KM (List Prf)
  deltaArgs sig ctx x es =
    kSigLookup sig x >>= \entryX => case entryX of
      Just (SigDef delta _ _ _) =>
        let entryTy : Nat -> List Elem -> Maybe Ty
            entryTy i pre = case getAt i (toList delta) of
              Just t => Just (substTy t (embed (cast pre)))
              Nothing => Nothing
        in statedArgs entryTy (toList es)
      _ => kerr "certificate: δ leaf at a non-definition '\{x}'"
   where
    statedArgs : (Nat -> List Elem -> Maybe Ty) -> List Elem -> KM (List Prf)
    statedArgs entryTy xs = go 0 xs []
     where
      go : Nat -> List Elem -> List Elem -> KM (List Prf)
      go i [] acc = pure []
      go i (e :: rest) acc = do
        ty <- case entryTy i (reverse acc) of
                Just t => pure t
                Nothing => kerr "certificate: spine entry type undetermined"
        q <- argPrf sig ctx e ty
        qs <- go (S i) rest (e :: acc)
        pure (q :: qs)

  ||| The spine of a path leaf stated entrywise at the reflected
  ||| telescope.
  pathArgs : Sig -> Ctx -> QSig -> Nat -> SubNorm -> KM (List Prf)
  pathArgs sig ctx sg k th = do
    sg' <- kQSig sig sg
    entry <- case qEntry sg' k of
               Just e => pure e
               Nothing => kerr "certificate: path leaf entry out of range"
    (tel, _, _) <- liftQ (reflTel sg' (qwAt k) entry)
    go tel 0 (toList th) []
   where
    go : List Ty -> Nat -> List Elem -> List Elem -> KM (List Prf)
    go tel i [] acc = pure []
    go tel i (e :: rest) acc = do
      ty <- case telInst tel i (reverse acc) of
              Just t => pure t
              Nothing => kerr "certificate: path leaf telescope mismatch"
      q <- argPrf sig ctx e ty
      qs <- go tel (S i) rest (e :: acc)
      pure (q :: qs)

  ||| A SKELETON for a term checked at a type, built from the kernel's
  ||| own exposure: the head exposures at intro forms (PExpose) and at
  ||| eliminations (PScrut) that a β-only checker cannot reach on its
  ||| own — the translator's twin of the elaborator's reconstruction.
  chkSkel : Sig -> Ctx -> Elem -> Ty -> KM Skel
  chkSkel sig ctx e ty = case e of
    PiIntro f => shaped (\t => case t of PiTy a b => Just (a, b); _ => Nothing) $ \(a, b) =>
      (\sk => Nd [] [sk]) <$> chkSkel sig (ctx :< a) f b
    SigmaIntro u v => shaped (\t => case t of SigmaTy a b => Just (a, b); _ => Nothing) $ \(a, b) =>
      [| (\su, sv => Nd [] [su, sv]) (chkSkel sig ctx u a) (chkSkel sig ctx v (substTy b (Ext Id u))) |]
    Inj1 a => shaped (\t => case t of SumTy d _ => Just d; _ => Nothing) $ \d =>
      (\sk => Nd [] [sk]) <$> chkSkel sig ctx a d
    Inj2 b => shaped (\t => case t of SumTy _ c => Just c; _ => Nothing) $ \c =>
      (\sk => Nd [] [sk]) <$> chkSkel sig ctx b c
    Class a => shaped (\t => case t of QuotTy d _ => Just d; _ => Nothing) $ \d =>
      (\sk => Nd [] [sk]) <$> chkSkel sig ctx a d
    Corec p a f x => shaped (\t => case t of NuTy pf => Just pf; _ => Nothing) $ \pf =>
      [| (\sa, sf, sx => Nd [] [sa, sf, sx]) (chkSkel sig ctx a UniverseTy)
                                              (chkSkel sig (ctx :< a) f (substTy (reflectPoly pf a) Wk))
                                              (chkSkel sig ctx x a) |]
    -- ⋆ at an EVIDENT prop: a squashed 𝟙, or an equation the join closes
    Star => do
      (tyX, pt) <- exposeK sig ctx ty
      ty' <- kWhnfT sig tyX
      case ty' of
        Squash sq => do
          sq' <- kWhnfT sig sq
          pure (case sq' of
                  OneTy => withExp pt tyX (Nd [PSquashWit OneIntro (Nd [] [])] [])
                  _ => withExp pt tyX (Nd [] []))
        Elem.EqTy _ _ _ => pure (withExp pt tyX (Nd [PReflEq PReflx] []))
        _ => pure (Nd [] [])
    ZeroElim t => (\sk => Nd [] [sk]) <$> chkSkel sig ctx t ZeroTy
    -- a constructor's or sort's spine, each entry at its telescope type
    QCtor sg k es => Nd [] <$> spineSkels sg k es
    QSort sg k es => Nd [] <$> spineSkels sg k es
    -- a QIIT eliminator checked at a type: the CONSTANT-MOTIVE instance
    -- (every sort's motive the expected type, weakened into the sort's
    -- context), the coherences by β (docs/NovaKernel.txt, A1/A4)
    QElim sg k mths es w => do
      sg' <- kQSig sig sg
      let sortPs = qPositions QKSort sg'
      let pointPs = qPositions QKPoint sg'
      let eqPs = qPositions QKEq sg'
      mots <- traverse (\sj => do
                sjE <- case qEntry sg' sj of
                         Just x => pure x
                         Nothing => kerr "certificate: sort out of range"
                (tel, _, _) <- liftQ (reflTel sg' (qwAt sj) sjE)
                pure (substTy ty (wkN (S (length tel))))) sortPs
      mSks <- traverse (\(cj, m) => do
                mty <- liftQ (methodTy sg' mots cj)
                chkSkel sig ctx m mty) (zip pointPs mths)
      let esL = toList es
      eSks <- traverse (\(i, x) => case qSpineChildTy sg' k es i of
                          Just t => chkSkel sig ctx x t
                          Nothing => pure (Nd [] [])) (zip (indices esL) esL)
      wSk <- chkSkel sig ctx w (QSort sg' k es)
      pure (Nd [PQMotives mots (map (const (Nd [] [])) mots), PQCoh (map (const PReflx) eqPs)]
               (mSks ++ eSks ++ [wSk]))
    -- a non-intro term at a type spelled otherwise than the one it
    -- infers to: the switch proof (a δ bridge) rides along, since the
    -- kernel's switch-less fallthrough compares by β only
    _ => do
      (sk, mty) <- infSkel sig ctx e
      case mty of
        Just t => do
          ok <- tyAgreeB sig ty t
          if ok then pure sk else do
            md <- deltaPrf sig t ty
            pure (case (md, sk) of
                    (Just p, Nd ps cs) => Nd (PSwitch p :: ps) cs
                    (Nothing, _) => sk)
        Nothing => pure sk
   where
    indices : List a -> List Nat
    indices xs = go 0 xs
     where
      go : Nat -> List a -> List Nat
      go _ [] = []
      go i (_ :: rest) = i :: go (S i) rest
    spineSkels : QSig -> Nat -> SubNorm -> KM (List Skel)
    spineSkels sg k es = do
      sg' <- kQSig sig sg
      let esL = toList es
      traverse (\(i, x) => case qSpineChildTy sg' k es i of
                             Just t => chkSkel sig ctx x t
                             Nothing => fst <$> infSkel sig ctx x) (zip (indices esL) esL)
    withExp : Prf -> Ty -> Skel -> Skel
    withExp PReflx _ sk = sk
    withExp pt tyX (Nd ps cs) = Nd (PExpose tyX pt :: ps) cs
    shaped : (Ty -> Maybe a) -> (a -> KM Skel) -> KM Skel
    shaped pick k = do
      (tyX, pt) <- exposeK sig ctx ty
      ty' <- kWhnfT sig tyX
      case pick ty' of
        Just parts => withExp pt tyX <$> k parts
        Nothing => pure (Nd [] [])

  ||| Inference position: the skeleton and the type it infers to
  ||| (Nothing when structure alone does not determine it).
  infSkel : Sig -> Ctx -> Elem -> KM (Skel, Maybe Ty)
  infSkel sig ctx e = case e of
    PiApp f a => do
      (fSk, fTy) <- infSkel sig ctx f
      case fTy of
        Just t => do
          (tX, pt) <- exposeK sig ctx t
          t' <- kWhnfT sig tX
          case t' of
            PiTy dom cod => do
              aSk <- chkSkel sig ctx a dom
              pure (withScrutK pt tX (Nd [] [fSk, aSk]), Just (substTy cod (Ext Id a)))
            _ => pure (Nd [] [fSk, Nd [] []], Nothing)
        Nothing => pure (Nd [] [fSk, Nd [] []], Nothing)
    SigmaElim1 t => scrut t (\t' => case t' of SigmaTy a _ => Just a; _ => Nothing)
    SigmaElim2 t => scrut t (\t' => case t' of SigmaTy _ b => Just (substTy b (Ext Id (SigmaElim1 t))); _ => Nothing)
    Out t => scrut t (\t' => case t' of NuTy f => Just (reflectPoly f (Elem.NuTy f)); _ => Nothing)
    NatIntro1 t => (\sk => (Nd [] [sk], Just NatTy)) <$> chkSkel sig ctx t NatTy
    Elem.EqTy l r t => do
      sl <- chkSkel sig ctx l t
      sr <- chkSkel sig ctx r t
      (st, _) <- infSkel sig ctx t
      pure (Nd [] [sl, sr, st], Just PropTy)
    Squash t => (\(sk, _) => (Nd [] [sk], Just PropTy)) <$> infSkel sig ctx t
    _ => do
      mt <- inferHead sig ctx e
      pure (Nd [] [], mt)
   where
    withScrutK : Prf -> Ty -> Skel -> Skel
    withScrutK PReflx _ sk = sk
    withScrutK pt tyX (Nd ps cs) = Nd (PScrut tyX pt :: ps) cs
    scrut : Elem -> (Ty -> Maybe Ty) -> KM (Skel, Maybe Ty)
    scrut t pick = do
      (tSk, tTy) <- infSkel sig ctx t
      case tTy of
        Just x => do
          (xX, pt) <- exposeK sig ctx x
          x' <- kWhnfT sig xX
          pure (withScrutK pt xX (Nd [] [tSk]), pick x')
        Nothing => pure (Nd [] [tSk], Nothing)

  ||| A TYPED NEUTRAL: the spine as a synthesising proof — self leaves
  ||| at the head, elimination nodes above, an ascription (PAt with a
  ||| δ proof) wherever a definition hides the shape the next
  ||| elimination needs — and the type it states.
  elemToPrf : Sig -> Ctx -> Elem -> KM (Prf, Ty)
  elemToPrf sig ctx e = case e of
    PiApp f a => do
      (pf, fTy) <- elemToPrf sig ctx f
      (fTyX, pt) <- exposeK sig ctx fTy
      fTy' <- kWhnfT sig fTyX
      case fTy' of
        PiTy dom cod => do
          pa <- argPrf sig ctx a dom
          pure (CPiApp (ascribe pf fTyX pt) pa, substTy cod (Ext Id a))
        _ => kerr "certificate: typed neutral applies a non-function [\{show f} : \{show fTy'}]"
    SigmaElim1 t => do
      (pt', tTy) <- elemToPrf sig ctx t
      (tTyX, pt) <- exposeK sig ctx tTy
      tTy' <- kWhnfT sig tTyX
      case tTy' of
        SigmaTy a _ => pure (CSigmaElim1 (ascribe pt' tTyX pt), a)
        _ => kerr "certificate: typed neutral projects a non-pair [\{show t} : \{show tTy'}]"
    SigmaElim2 t => do
      (pt', tTy) <- elemToPrf sig ctx t
      (tTyX, pt) <- exposeK sig ctx tTy
      tTy' <- kWhnfT sig tTyX
      case tTy' of
        SigmaTy _ b => pure (CSigmaElim2 (ascribe pt' tTyX pt), substTy b (Ext Id (SigmaElim1 t)))
        _ => kerr "certificate: typed neutral projects a non-pair [\{show t} : \{show tTy'}]"
    Out t => do
      (pt', tTy) <- elemToPrf sig ctx t
      (tTyX, pt) <- exposeK sig ctx tTy
      tTy' <- kWhnfT sig tTyX
      case tTy' of
        NuTy f => pure (COut (ascribe pt' tTyX pt), reflectPoly f (Elem.NuTy f))
        _ => kerr "certificate: typed neutral observes a non-ν element [\{show t} : \{show tTy'}]"
    _ => do
      (_, _, ty) <- kPrfS sig ctx (PSelf e)
      pure (PSelf e, ty)
   where
    ascribe : Prf -> Ty -> Prf -> Prf
    ascribe p _ PReflx = p
    ascribe p tyX pt = PAt p tyX pt

  ||| A proof ARGUMENT at the domain the head demands: a spine states
  ||| its type and is ascribed to the domain when spelled otherwise; any
  ||| other form is checked at the domain (PChk, with its skeleton).
  argPrf : Sig -> Ctx -> Elem -> Ty -> KM Prf
  argPrf sig ctx a dom =
    if isSpine a
      then do
        (pa, aTy) <- elemToPrf sig ctx a
        ok <- tyAgreeB sig dom aTy
        if ok then pure pa else do
          md <- deltaPrf sig aTy dom
          case md of
            Just pt => pure (PAt pa dom pt)
            Nothing => kerr "certificate: proof argument at the wrong type [stated: \{show aTy}; expected: \{show dom}]"
      else do
        sk <- chkSkel sig ctx a dom
        pure (PChk a dom sk)

||| The head of an elimination as a proof child: reflexivity when its
||| declared type already shows the shape the node needs (β), else the
||| typed neutral that states it. Returns the (exposed) type as well.
headPrf : Sig -> Ctx -> Elem -> KM (Maybe Ty, Prf)
headPrf sig ctx hd = do
  hTy <- inferHead sig ctx hd
  case hTy of
    Nothing =>
      if isSpine hd
        then do (p, t) <- elemToPrf sig ctx hd; pure (Just t, p)
        else pure (Nothing, PReflx)
    Just t => do
      (tX, pt) <- exposeK sig ctx t
      case pt of
        PReflx => pure (Just t, PReflx)
        _ => do (p, t') <- elemToPrf sig ctx hd; pure (Just t', p)

||| The classifier a shared former's components sit at, as the kernel
||| reads it (compClassifier).
classifierOf : Sig -> Maybe Ty -> KM Ty
classifierOf sig mty = compClassifier sig mty

||| The domain of a function's type, as the kernel's app node reads it
||| (β-whnf only).
domOf : Sig -> Maybe Ty -> KM (Maybe Ty)
domOf sig Nothing = pure Nothing
domOf sig (Just t) = do
  t' <- kWhnfT sig t
  pure (case t' of
          PiTy dom _ => Just dom
          _ => Nothing)

||| The congruence skeleton along a path, TYPED: the position's context
||| and expected type are computed as the kernel's nodes compute them
||| (the type flowing down, a neutral head's inferred type, the
||| constant-motive reading), and a node that needs a shape the type
||| only exposes by δ is wrapped in the conversion. `leaf` acts at the
||| path's end with the context, the type (Nothing: undetermined), the
||| binders crossed and the subterm there, giving the leaf's proof and
||| the replacement; every sibling is reflexivity. Child indexing as
||| the engine's rewriter counts it.
wrapAt : Sig -> Ctx -> Maybe Ty -> Nat -> Elem -> List Nat
      -> (Ctx -> Maybe Ty -> Nat -> Elem -> KM (Prf, Elem)) -> KM (Prf, Elem)
wrapAt sig ctx mty b u [] leaf = leaf ctx mty b u
wrapAt sig ctx mty b u (i :: p) leaf = do
  let go : Ctx -> Maybe Ty -> Nat -> Elem -> KM (Prf, Elem)
      go ctx' mty' b' x = wrapAt sig ctx' mty' b' x p leaf
  -- a shape the node needs from the type flowing down, with the
  -- conversion that exposes it
  let shaped : String -> (Ty -> Maybe a) -> ((a, Prf -> Prf) -> KM (Prf, Elem)) -> KM (Prf, Elem)
      shaped what pick k = do
        ty <- case mty of
                Just t => pure t
                Nothing => kerr "certificate: \{what} at a type-undetermined position"
        (tyX, pt) <- exposeK sig ctx ty
        tyW <- kWhnfT sig tyX
        case pick tyW of
          Just parts => k (parts, convWrap pt tyX)
          Nothing => kerr "certificate: \{what} at a type without the shape [\{show tyW}]"
  case (u, i) of
    (ZeroElim t, 0) => (\(q, t') => (CZeroElim q, ZeroElim t')) <$> go ctx (Just ZeroTy) b t
    (NatIntro1 t, 0) => (\(q, t') => (CNatIntro1 q, NatIntro1 t')) <$> go ctx (Just NatTy) b t
    (NatElim z s t, 0) => (\(q, z') => (CNatElim Nothing q PReflx PReflx, NatElim z' s t)) <$> go ctx mty b z
    (NatElim z s t, 1) =>
      (\(q, s') => (CNatElim Nothing PReflx q PReflx, NatElim z s' t))
        <$> go (ctx :< NatTy :< fromMaybe TopTy (map (\x => substTy x Wk) mty)) (map (\x => substTy x (wkN 2)) mty) (2 + b) s
    (NatElim z s t, 2) => (\(q, t') => (CNatElim Nothing PReflx PReflx q, NatElim z s t')) <$> go ctx (Just NatTy) b t
    (PiIntro f, 0) =>
      shaped "λ-congruence" (\t => case t of PiTy a c => Just (a, c); _ => Nothing) $ \((a, c), conv) =>
        (\(q, f') => (conv (CPiIntro q), PiIntro f')) <$> go (ctx :< a) (Just c) (1 + b) f
    (PiApp f e, 0) => do
      fTy <- inferHead sig ctx f
      (\(q, f') => (CPiApp q PReflx, PiApp f' e)) <$> go ctx fTy b f
    (PiApp f e, 1) => do
      (fTy, pf) <- headPrf sig ctx f
      aTy <- domOf sig fTy
      (\(q, e') => (CPiApp pf q, PiApp f e')) <$> go ctx aTy b e
    (SigmaElim1 t, 0) => do
      tTy <- inferHead sig ctx t
      (\(q, t') => (CSigmaElim1 q, SigmaElim1 t')) <$> go ctx tTy b t
    (SigmaElim2 t, 0) => do
      tTy <- inferHead sig ctx t
      (\(q, t') => (CSigmaElim2 q, SigmaElim2 t')) <$> go ctx tTy b t
    (Inj1 t, 0) =>
      shaped "inj₁ congruence" (\ty => case ty of SumTy a _ => Just a; _ => Nothing) $ \(a, conv) =>
        (\(q, t') => (conv (CInj1 q), Inj1 t')) <$> go ctx (Just a) b t
    (Inj2 t, 0) =>
      shaped "inj₂ congruence" (\ty => case ty of SumTy _ c => Just c; _ => Nothing) $ \(c, conv) =>
        (\(q, t') => (conv (CInj2 q), Inj2 t')) <$> go ctx (Just c) b t
    (SumElim l r t, 0) => do
      ((a, _), pt) <- sumParts t
      (\(q, l') => (CSumElim Nothing q PReflx pt, SumElim l' r t)) <$> go (ctx :< a) Nothing (1 + b) l
    (SumElim l r t, 1) => do
      ((_, c), pt) <- sumParts t
      (\(q, r') => (CSumElim Nothing PReflx q pt, SumElim l r' t)) <$> go (ctx :< c) Nothing (1 + b) r
    (SumElim l r t, 2) => do
      tTy <- inferHead sig ctx t
      (\(q, t') => (CSumElim Nothing PReflx PReflx q, SumElim l r t')) <$> go ctx tTy b t
    (SigmaIntro x y, 0) =>
      shaped "pair congruence" (\ty => case ty of SigmaTy a c => Just (a, c); _ => Nothing) $ \((a, c), conv) =>
        (\(q, x') => (conv (CSigmaIntro q PReflx), SigmaIntro x' y)) <$> go ctx (Just a) b x
    (SigmaIntro x y, 1) =>
      shaped "pair congruence" (\ty => case ty of SigmaTy a c => Just (a, c); _ => Nothing) $ \((a, c), conv) =>
        (\(q, y') => (conv (CSigmaIntro PReflx q), SigmaIntro x y')) <$> go ctx (Just (substTy c (Ext Id x))) b y
    (Elem.PiTy a c, 0) => do
      cls <- classifierOf sig mty
      (\(q, a') => (CPiTy q PReflx, Elem.PiTy a' c)) <$> go ctx (Just cls) b a
    (Elem.PiTy a c, 1) => do
      cls <- classifierOf sig mty
      (\(q, c') => (CPiTy PReflx q, Elem.PiTy a c')) <$> go (ctx :< a) (Just cls) (1 + b) c
    (Elem.SigmaTy a c, 0) => do
      cls <- classifierOf sig mty
      (\(q, a') => (CSigmaTy q PReflx, Elem.SigmaTy a' c)) <$> go ctx (Just cls) b a
    (Elem.SigmaTy a c, 1) => do
      cls <- classifierOf sig mty
      (\(q, c') => (CSigmaTy PReflx q, Elem.SigmaTy a c')) <$> go (ctx :< a) (Just cls) (1 + b) c
    (Elem.SumTy a c, 0) => do
      cls <- classifierOf sig mty
      (\(q, a') => (CSumTy q PReflx, Elem.SumTy a' c)) <$> go ctx (Just cls) b a
    (Elem.SumTy a c, 1) => do
      cls <- classifierOf sig mty
      (\(q, c') => (CSumTy PReflx q, Elem.SumTy a c')) <$> go ctx (Just cls) b c
    (Elem.EqTy l r t, 0) => (\(q, l') => (CEqTy q PReflx PReflx, Elem.EqTy l' r t)) <$> go ctx (Just t) b l
    (Elem.EqTy l r t, 1) => (\(q, r') => (CEqTy PReflx q PReflx, Elem.EqTy l r' t)) <$> go ctx (Just t) b r
    (Elem.EqTy l r t, 2) => (\(q, t') => (CEqTy PReflx PReflx q, Elem.EqTy l r t')) <$> go ctx (Just TopTy) b t
    (QuotTy a r, 0) => do
      cls <- classifierOf sig mty
      (\(q, a') => (CQuotTy q PReflx, QuotTy a' r)) <$> go ctx (Just cls) b a
    (QuotTy a r, 1) =>
      (\(q, r') => (CQuotTy PReflx q, QuotTy a r')) <$> go (ctx :< a :< substTy a Wk) (Just PropTy) (2 + b) r
    (SigVar x es, _) => do
      cty <- sigChildTy sig x (toList es) i
      (\(qs, es') => (CSigVar x qs, SigVar x es')) <$> spineWrap i es (go ctx cty b)
    (Class a, 0) =>
      shaped "class congruence" (\ty => case ty of QuotTy dom _ => Just dom; _ => Nothing) $ \(dom, conv) =>
        (\(q, a') => (conv (CClass q), Class a')) <$> go ctx (Just dom) b a
    (Out t, 0) => do
      tTy <- inferHead sig ctx t
      (\(q, t') => (COut q, Out t')) <$> go ctx tTy b t
    (Corec pf a f x, 0) => (\(q, a') => (CCorec pf q PReflx PReflx, Corec pf a' f x)) <$> go ctx (Just UniverseTy) b a
    (Corec pf a f x, 1) => (\(q, f') => (CCorec pf PReflx q PReflx, Corec pf a f' x)) <$> go (ctx :< a) Nothing (1 + b) f
    (Corec pf a f x, 2) => (\(q, x') => (CCorec pf PReflx PReflx q, Corec pf a f x')) <$> go ctx (Just a) b x
    (QuotElim f q0, 0) => do
      ((a, _), pq) <- quotParts q0
      (\(q, f') => (CQuotElim Nothing q pq, QuotElim f' q0)) <$> go (ctx :< a) Nothing (1 + b) f
    (QuotElim f q0, 1) => do
      qTy <- inferHead sig ctx q0
      (\(q, q0') => (CQuotElim Nothing PReflx q, QuotElim f q0')) <$> go ctx qTy b q0
    (Squash t, 0) => (\(q, t') => (CSquash q, Squash t')) <$> go ctx (Just TopTy) b t
    (QSort sg k es, _) =>
      (\(qs, es') => (CQSort sg k qs, QSort sg k es')) <$> spineWrap i es (go ctx (qSpineChildTy sg k es i) b)
    (QCtor sg k es, _) =>
      (\(qs, es') => (CQCtor sg k qs, QCtor sg k es')) <$> spineWrap i es (go ctx (qSpineChildTy sg k es i) b)
    (QElim sg k fs es w, _) =>
      if i == length (toList es)
        then (\(q, w') => (CQElim sg k Nothing (map (const PReflx) fs) (map (const PReflx) (toList es)) q, QElim sg k fs es w'))
               <$> go ctx (Just (QSort sg k es)) b w
        else (\(qs, es') => (CQElim sg k Nothing (map (const PReflx) fs) qs PReflx, QElim sg k fs es' w))
               <$> spineWrap i es (go ctx (qSpineChildTy sg k es i) b)
    _ => kerr "certificate: bad path [i=\{show i}, at \{show u}]"
 where
  -- the scrutinee as a proof child (a typed neutral when its declared
  -- type hides the shape) and the shape's parts
  sumParts : Elem -> KM ((Ty, Ty), Prf)
  sumParts t = do
    (tTy, pt) <- headPrf sig ctx t
    case tTy of
      Just x => do
        x' <- kWhnfT sig x
        pure (case x' of
                SumTy a c => ((a, c), pt)
                _ => ((TopTy, TopTy), pt))
      Nothing => pure ((TopTy, TopTy), pt)
  quotParts : Elem -> KM ((Ty, Ty), Prf)
  quotParts q = do
    (qTy, pq) <- headPrf sig ctx q
    case qTy of
      Just x => do
        x' <- kWhnfT sig x
        pure (case x' of
                QuotTy a r => ((a, r), pq)
                _ => ((TopTy, TopTy), pq))
      Nothing => pure ((TopTy, TopTy), pq)

mutual
  ||| The steps applied in order to a β-joined side: the proof (a
  ||| right-nested chain ending in reflexivity, so the kernel runs every
  ||| link directionally and compares only at the end) and the joined
  ||| result.
  chainOn : Sig -> Ctx -> Ty -> Elem -> List Step -> KM (Prf, Elem)
  chainOn sig ctx tyRoot t [] = pure (PReflx, t)
  chainOn sig ctx tyRoot t (s :: rest) = do
    (p1, t1) <- stepOn sig ctx tyRoot t s
    t1J <- kJoinElem sig t1
    (p2, t2) <- chainOn sig ctx tyRoot t1J rest
    pure (PTrans p1 p2, t2)

  ||| One step on a side: the licence's proof wrapped in the congruence
  ||| skeleton along the path (weakened by the binders crossed — a
  ||| licence is spelled in the root context), and the rewritten side.
  stepOn : Sig -> Ctx -> Ty -> Elem -> Step -> KM (Prf, Elem)
  stepOn sig ctx tyRoot t step =
    case (step.lic, step.flip, step.sels, step.path) of
      (LUnfoldAll ns, False, [], []) => do
        t' <- unfoldAllK sig ns t
        pure (PDeltaAll ns, t')
      (LUnfoldAll _, _, _, _) => kerr "certificate: an unfold-all step acts at the root, forward"
      -- forward unfold: the spine is spelled at the occurrence
      (LUnfold x es, False, [], path) =>
        kSigLookup sig x >>= \entryX => case entryX of
          Just (SigDef _ _ body _) =>
            wrapAt sig ctx (Just tyRoot) 0 t path (\_, _, b, u => case u of
                SigVar y es' =>
                  if y == x then do
                      qs <- deltaArgs sig ctx x es
                      pure (PDelta x qs, substElem body (embed es'))
                    else kerr "certificate: unfold step at a reference to '\{y}', licensed for '\{x}'"
                _ => kerr "certificate: unfold step at a non-reference")
          _ => kerr "certificate: unfold step at a non-definition '\{x}'"
      _ => do
        (leaf, _, rN, lty) <- leafOf sig ctx step
        wrapAt sig ctx (Just tyRoot) 0 t step.path (\ctx', mty, b, _ => do
          let leafW = substPrf leaf (wkN b)
          let ltyW = substTy lty (wkN b)
          -- the positional match: the stated equation's type meets the
          -- position's by β, or arrives converted
          leafP <- case mty of
            Nothing => pure leafW
            Just e => do
              ok <- tyAgreeB sig e ltyW
              if ok then pure leafW else do
                md <- deltaPrf sig ltyW e
                case md of
                  Just pt => pure (PAt leafW e pt)
                  Nothing => kerr "certificate: no δ-conversion between the stated type and the position's [stated: \{show ltyW}; position: \{show e}]"
          pure (leafP, substElem rN (wkN b)))

  ||| A licence as the kernel reads it — its proof leaf with selectors,
  ||| licence normalization and orientation — and the equation it
  ||| effectively licenses (sides β-joined), in the root context.
  leafOf : Sig -> Ctx -> Step -> KM (Prf, Elem, Elem, Ty)
  leafOf sig ctx step = do
    base <- case step.lic of
      LProof p => do
        -- the proof element as a TYPED NEUTRAL (self leaves, elimination
        -- nodes, ascriptions where a definition hides a shape), its type
        -- exposed to its ≡ by recorded δ — an ascription again
        (pp, pty) <- elemToPrf sig ctx p
        (ptyX, pt) <- exposeK sig ctx pty
        pure (case pt of
                PReflx => PRefl pp
                _ => PRefl (PAt pp ptyX pt))
      LPath sg k th => PPath sg k <$> pathArgs sig ctx sg k th
      LUnfold x es => PDelta x <$> deltaArgs sig ctx x es
      LUnfoldAll _ => kerr "certificate: an unfold-all step is forward-only, at the root"
    -- selectors match heads on the β-joined sides: a side whose head
    -- δ hides arrives exposed, by transitivity over the leaf; a
    -- selector's instantiation element is stated at the domain the
    -- current sides show
    base' <- case step.sels of
      [] => pure base
      _ => do
        (l0, r0, _) <- kPrfS sig ctx base
        (_, pl) <- exposeK sig ctx l0
        (_, pr) <- exposeK sig ctx r0
        pure (pTrans (pSym pl) (pTrans base pr))
    leaf0 <- selectors sig ctx base' step.sels
    (l, r, lty) <- kPrfS sig ctx leaf0
    lJ <- kJoinElem sig l
    rJ <- kJoinElem sig r
    (pL, lN) <- chainOn sig ctx lty lJ (filter (\s => s.onLhs) step.licNorm)
    (pR, rN) <- chainOn sig ctx lty rJ (filter (\s => not s.onLhs) step.licNorm)
    let leaf = pTrans (pSym pL) (pTrans leaf0 pR)
    pure (if step.flip then (pSym leaf, rN, lN, lty) else (leaf, lN, rN, lty))

  ||| The selectors applied in order, each instantiation element stated
  ||| (a typed neutral or a checked leaf) at the domain of the sides the
  ||| selectors so far leave.
  selectors : Sig -> Ctx -> Prf -> List ESel -> KM Prf
  selectors sig ctx q [] = pure q
  selectors sig ctx q (sel :: rest) = do
    (l, r, _) <- kPrfS sig ctx q
    r' <- kJoinElem sig r
    ksel <- case sel of
      ESelSuc => pure SelSuc
      ESelDom => pure SelDom
      ESelSumL => pure SelSumL
      ESelSumR => pure SelSumR
      ESelQDom => pure SelQDom
      ESelQIdx i => pure (SelQIdx i)
      ESelCod u => case r' of
        Elem.PiTy a1 _ => SelCod <$> argPrf sig ctx u a1
        Elem.SigmaTy a1 _ => SelCod <$> argPrf sig ctx u a1
        _ => kerr "certificate: codomain selector at a non-binder equation"
      ESelQRel u v => case r' of
        QuotTy a1 _ => [| SelQRel (argPrf sig ctx u a1) (argPrf sig ctx v a1) |]
        _ => kerr "certificate: relation selector at a non-quotient equation"
    selectors sig ctx (PSel ksel q) rest

  ||| A type's reconstructed skeleton — for a prop-ness question the
  ||| kernel answers by inference (bare where nothing reconstructs).
  tySkel : Sig -> Ctx -> Ty -> KM Skel
  tySkel sig ctx t = kOrElse (fst <$> infSkel sig ctx t) (pure (Nd [] []))

  ||| The final as a proof at the rewritten sides.
  finalPrf : Sig -> Ctx -> Final -> Elem -> Elem -> Ty -> KM Prf
  finalPrf sig ctx FBeta l r ty = pure PReflx
  finalPrf sig ctx FProp l r ty = do
    (tyX, pt) <- exposeK sig ctx ty
    sk <- tySkel sig ctx tyX
    pure (convWrap pt tyX (PIrrel sk))
  finalPrf sig ctx (FWitness Nothing) l r ty = do
    (tyX, pt) <- exposeK sig ctx ty
    pure (convWrap pt tyX (PQuotWit Nothing))
  finalPrf sig ctx (FWitness (Just c)) l r ty = do
    (tyX, pt) <- exposeK sig ctx ty
    ty' <- kWhnfT sig tyX
    case (l, r, ty') of
      (Class a, Class b, QuotTy _ rel) => do
        relInst <- kJoinElem sig (substElem rel (Ext (Ext Id a) b))
        case relInst of
          Elem.EqTy wl wr wt => convWrap pt tyX . PQuotWit . Just <$> toPrfK sig ctx c wl wr wt
          _ => pure (convWrap pt tyX (PQuotWit Nothing))
      _ => kerr "certificate: witness final at a non-class equation"
  finalPrf sig ctx (FWitnessPrf w sk) l r ty = do
    (tyX, pt) <- exposeK sig ctx ty
    pure (convWrap pt tyX (PQuotWitPrf w sk))
  finalPrf sig ctx (FInj c) l r ty = do
    (tyX, pt) <- exposeK sig ctx ty
    ty' <- kWhnfT sig tyX
    case (l, r, ty') of
      (Inj1 x, Inj1 y, SumTy a _) => convWrap pt tyX . PInj <$> toPrfK sig ctx c x y a
      (Inj2 x, Inj2 y, SumTy _ b) => convWrap pt tyX . PInj <$> toPrfK sig ctx c x y b
      _ => kerr "certificate: injection final at a non-matching equation"
  finalPrf sig ctx (FEtaPi c) l r ty = do
    (tyX, pt) <- exposeK sig ctx ty
    ty' <- kWhnfT sig tyX
    case ty' of
      PiTy dom cod =>
        convWrap pt tyX . PEtaPi <$> toPrfK sig (ctx :< dom) c
                     (PiApp (substElem l Wk) (CtxVar 0))
                     (PiApp (substElem r Wk) (CtxVar 0)) cod
      _ => kerr "certificate: Π-η final at a non-Π type"
  finalPrf sig ctx (FEtaSigma c1 c2) l r ty = do
    (tyX, pt) <- exposeK sig ctx ty
    ty' <- kWhnfT sig tyX
    case ty' of
      SigmaTy dom cod =>
        convWrap pt tyX <$>
          [| PEtaSigma (toPrfK sig ctx c1 (SigmaElim1 l) (SigmaElim1 r) dom)
                       (toPrfK sig ctx c2 (SigmaElim2 l) (SigmaElim2 r) (substTy cod (Ext Id (SigmaElim1 l)))) |]
      _ => kerr "certificate: Σ-η final at a non-Σ type"
  finalPrf sig ctx (FPropExt f fs g gs) l r ty = do
    (tyX, pt) <- exposeK sig ctx ty
    pure (convWrap pt tyX (PPropExt f fs g gs))
  finalPrf sig ctx (FPrfCong c) l r ty =
    [| PPrfCong (tySkel sig ctx l) (tySkel sig ctx r) (toPrfK sig ctx c l r PropTy) |]
  finalPrf sig ctx (FQuotCong c) l r ty =
    case (l, r) of
      (QuotTy d0 r0, QuotTy d1 r1) =>
        CQuotTy PReflx <$> toPrfK sig (ctx :< d1 :< substTy d1 Wk) c r0 r1 PropTy
      _ => kerr "certificate: quotient-congruence final at non-quotient types"
  finalPrf sig ctx (FPiCong dc cc) l r ty =
    case (l, r) of
      (Elem.PiTy d0 c0, Elem.PiTy d1 c1) =>
        [| CPiTy (toPrfK sig ctx dc d0 d1 TopTy) (toPrfK sig (ctx :< d1) cc c0 c1 TopTy) |]
      _ => kerr "certificate: Π-congruence final at non-Π types"
  finalPrf sig ctx (FSigmaCong dc cc) l r ty =
    case (l, r) of
      (Elem.SigmaTy d0 c0, Elem.SigmaTy d1 c1) =>
        [| CSigmaTy (toPrfK sig ctx dc d0 d1 TopTy) (toPrfK sig (ctx :< d1) cc c0 c1 TopTy) |]
      _ => kerr "certificate: Σ-congruence final at non-Σ types"
  finalPrf sig ctx (FSumCong lc rc) l r ty =
    case (l, r) of
      (Elem.SumTy l0 r0, Elem.SumTy l1 r1) =>
        [| CSumTy (toPrfK sig ctx lc l0 l1 TopTy) (toPrfK sig ctx rc r0 r1 TopTy) |]
      _ => kerr "certificate: ⊎-congruence final at non-⊎ types"
  finalPrf sig ctx (FChain points certs) l r ty =
    goLinks (l :: map fst points ++ [r]) certs
   where
    goLinks : List Elem -> List ECert -> KM Prf
    goLinks [a, b] [c] = toPrfK sig ctx c a b ty
    goLinks (a :: b :: rest) (c :: cs) = do
      q <- toPrfK sig ctx c a b ty
      q' <- goLinks (b :: rest) cs
      pure (PTransAt q b q')
    goLinks _ _ = kerr "certificate: chain points and links do not match up"

  ||| A certificate for Γ ⊢ l ≐ r : ty as a proof term.
  toPrfK : Sig -> Ctx -> ECert -> Elem -> Elem -> Ty -> KM Prf
  toPrfK sig ctx (MkECertF bridge steps final) l r ty = do
    let tyU = case bridge of
                Nothing => ty
                Just (tyX, _) => tyX
    l0 <- kJoinElem sig l
    r0 <- kJoinElem sig r
    (pL, l1) <- chainOn sig ctx tyU l0 (filter (\s => s.onLhs) steps)
    (pR, r1) <- chainOn sig ctx tyU r0 (filter (\s => not s.onLhs) steps)
    pF <- finalPrf sig ctx final l1 r1 tyU
    let body = pTrans pL (pTrans pF (pSym pR))
    case bridge of
      Nothing => pure body
      Just (tyX, c) => do
        pT <- toPrfK sig ctx c ty tyX TopTy
        pure (PConv pT tyX body)

||| Fuel for the translation (the kernel's own budget).
export
certFuel : Nat
certFuel = 1000000

||| A path leaf's spine stated (for the elaborator's own path leaves).
export
pathArgsB : Sig -> Ctx -> QSig -> Nat -> SubNorm -> Maybe (List Prf)
pathArgsB sig ctx sg k th =
  case runKM (pathArgs sig ctx sg k th) certFuel of
    Right (qs, _) => Just qs
    Left _ => Nothing

||| A proof element as a reflected typed neutral (for the elaborator's
||| own proof leaves).
export
prfOfElem : Sig -> Ctx -> Elem -> Maybe Prf
prfOfElem sig ctx p =
  case runKM (do (pp, pty) <- elemToPrf sig ctx p
                 (ptyX, pt) <- exposeK sig ctx pty
                 pure (case pt of
                         PReflx => PRefl pp
                         _ => PRefl (PAt pp ptyX pt))) certFuel of
    Right (q, _) => Just q
    Left _ => Nothing

||| Translate a certificate for Γ ⊢ l ≐ r : ty; Left = the certificate
||| does not even replay engine-side (the same signal a kernel
||| rejection gives).
export
toPrf : Sig -> Ctx -> ECert -> Elem -> Elem -> Ty -> Either String Prf
toPrf sig ctx c l r ty = map fst (runKM (toPrfK sig ctx c l r ty) certFuel)

||| Translate a type certificate (an element certificate at 𝕍).
export
toPrfTy : Sig -> Ctx -> ECert -> Ty -> Ty -> Either String Prf
toPrfTy sig ctx c a b = toPrf sig ctx c a b TopTy

||| Translate then check: the certificate replays iff its proof term
||| checks. Right = the proof term (what the item's skeleton carries).
export
replayElem : Sig -> Ctx -> ECert -> Elem -> Elem -> Ty -> Either String Prf
replayElem sig ctx c l r ty = do
  p <- toPrf sig ctx c l r ty
  kCheckEqElem sig ctx certFuel p l r ty
  pure p

export
replayTy : Sig -> Ctx -> ECert -> Ty -> Ty -> Either String Prf
replayTy sig ctx c a b = replayElem sig ctx c a b TopTy
