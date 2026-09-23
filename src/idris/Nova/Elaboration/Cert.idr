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
import Data.SnocList

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel.QIIT
import Nova.Kernel

%default covering

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
  sels : List Sel
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

||| The congruence skeleton along a path: `leaf` acts at the path's end
||| with the number of binders crossed and the subterm there, giving
||| the leaf's proof and the replacement; every sibling is reflexivity.
||| Child indexing as the engine's rewriter counts it.
wrapAt : Elem -> List Nat -> (Nat -> Elem -> KM (Prf, Elem)) -> Nat -> KM (Prf, Elem)
wrapAt u [] leaf b = leaf b u
wrapAt u (i :: p) leaf b = do
  let go : Nat -> Elem -> KM (Prf, Elem)
      go b' x = wrapAt x p leaf b'
  case (u, i) of
    (ZeroElim t, 0) => (\(q, t') => (CZeroElim q, ZeroElim t')) <$> go b t
    (NatIntro1 t, 0) => (\(q, t') => (CNatIntro1 q, NatIntro1 t')) <$> go b t
    (NatElim z s t, 0) => (\(q, z') => (CNatElim Nothing q PReflx PReflx, NatElim z' s t)) <$> go b z
    (NatElim z s t, 1) => (\(q, s') => (CNatElim Nothing PReflx q PReflx, NatElim z s' t)) <$> go (2 + b) s
    (NatElim z s t, 2) => (\(q, t') => (CNatElim Nothing PReflx PReflx q, NatElim z s t')) <$> go b t
    (PiIntro f, 0) => (\(q, f') => (CPiIntro q, PiIntro f')) <$> go (1 + b) f
    (PiApp f e, 0) => (\(q, f') => (CPiApp q PReflx, PiApp f' e)) <$> go b f
    (PiApp f e, 1) => (\(q, e') => (CPiApp PReflx q, PiApp f e')) <$> go b e
    (SigmaElim1 t, 0) => (\(q, t') => (CSigmaElim1 q, SigmaElim1 t')) <$> go b t
    (SigmaElim2 t, 0) => (\(q, t') => (CSigmaElim2 q, SigmaElim2 t')) <$> go b t
    (Inj1 t, 0) => (\(q, t') => (CInj1 q, Inj1 t')) <$> go b t
    (Inj2 t, 0) => (\(q, t') => (CInj2 q, Inj2 t')) <$> go b t
    (SumElim l r t, 0) => (\(q, l') => (CSumElim Nothing q PReflx PReflx, SumElim l' r t)) <$> go (1 + b) l
    (SumElim l r t, 1) => (\(q, r') => (CSumElim Nothing PReflx q PReflx, SumElim l r' t)) <$> go (1 + b) r
    (SumElim l r t, 2) => (\(q, t') => (CSumElim Nothing PReflx PReflx q, SumElim l r t')) <$> go b t
    (SigmaIntro x y, 0) => (\(q, x') => (CSigmaIntro q PReflx, SigmaIntro x' y)) <$> go b x
    (SigmaIntro x y, 1) => (\(q, y') => (CSigmaIntro PReflx q, SigmaIntro x y')) <$> go b y
    (Elem.PiTy a c, 0) => (\(q, a') => (CPiTy q PReflx, Elem.PiTy a' c)) <$> go b a
    (Elem.PiTy a c, 1) => (\(q, c') => (CPiTy PReflx q, Elem.PiTy a c')) <$> go (1 + b) c
    (Elem.SigmaTy a c, 0) => (\(q, a') => (CSigmaTy q PReflx, Elem.SigmaTy a' c)) <$> go b a
    (Elem.SigmaTy a c, 1) => (\(q, c') => (CSigmaTy PReflx q, Elem.SigmaTy a c')) <$> go (1 + b) c
    (Elem.SumTy a c, 0) => (\(q, a') => (CSumTy q PReflx, Elem.SumTy a' c)) <$> go b a
    (Elem.SumTy a c, 1) => (\(q, c') => (CSumTy PReflx q, Elem.SumTy a c')) <$> go b c
    (Elem.EqTy l r t, 0) => (\(q, l') => (CEqTy q PReflx PReflx, Elem.EqTy l' r t)) <$> go b l
    (Elem.EqTy l r t, 1) => (\(q, r') => (CEqTy PReflx q PReflx, Elem.EqTy l r' t)) <$> go b r
    (Elem.EqTy l r t, 2) => (\(q, t') => (CEqTy PReflx PReflx q, Elem.EqTy l r t')) <$> go b t
    (QuotTy a r, 0) => (\(q, a') => (CQuotTy q PReflx, QuotTy a' r)) <$> go b a
    (QuotTy a r, 1) => (\(q, r') => (CQuotTy PReflx q, QuotTy a r')) <$> go (2 + b) r
    (SigVar x es, _) => (\(qs, es') => (CSigVar x qs, SigVar x es')) <$> spineWrap i es (go b)
    (Class a, 0) => (\(q, a') => (CClass q, Class a')) <$> go b a
    (Out t, 0) => (\(q, t') => (COut q, Out t')) <$> go b t
    (Corec pf a f x, 0) => (\(q, a') => (CCorec pf q PReflx PReflx, Corec pf a' f x)) <$> go b a
    (Corec pf a f x, 1) => (\(q, f') => (CCorec pf PReflx q PReflx, Corec pf a f' x)) <$> go (1 + b) f
    (Corec pf a f x, 2) => (\(q, x') => (CCorec pf PReflx PReflx q, Corec pf a f x')) <$> go b x
    (QuotElim f q0, 0) => (\(q, f') => (CQuotElim Nothing q PReflx, QuotElim f' q0)) <$> go (1 + b) f
    (QuotElim f q0, 1) => (\(q, q0') => (CQuotElim Nothing PReflx q, QuotElim f q0')) <$> go b q0
    (Squash t, 0) => (\(q, t') => (CSquash q, Squash t')) <$> go b t
    (QSort sg k es, _) => (\(qs, es') => (CQSort sg k qs, QSort sg k es')) <$> spineWrap i es (go b)
    (QCtor sg k es, _) => (\(qs, es') => (CQCtor sg k qs, QCtor sg k es')) <$> spineWrap i es (go b)
    (QElim sg k ms fs es w, _) =>
      if i == length (toList es)
        then (\(q, w') => (CQElim sg k ms fs (map (const PReflx) (toList es)) q, QElim sg k ms fs es w')) <$> go b w
        else (\(qs, es') => (CQElim sg k ms fs qs PReflx, QElim sg k ms fs es' w)) <$> spineWrap i es (go b)
    _ => kerr "certificate: bad path [i=\{show i}, at \{show u}]"

mutual
  ||| The steps applied in order to a β-joined side: the proof (a
  ||| right-nested chain ending in reflexivity, so the kernel runs every
  ||| link directionally and compares only at the end) and the joined
  ||| result.
  chainOn : Sig -> Ctx -> Elem -> List Step -> KM (Prf, Elem)
  chainOn sig ctx t [] = pure (PReflx, t)
  chainOn sig ctx t (s :: rest) = do
    (p1, t1) <- stepOn sig ctx t s
    t1J <- kJoinElem sig t1
    (p2, t2) <- chainOn sig ctx t1J rest
    pure (PTrans p1 p2, t2)

  ||| One step on a side: the licence's proof wrapped in the congruence
  ||| skeleton along the path (weakened by the binders crossed — a
  ||| licence is spelled in the root context), and the rewritten side.
  stepOn : Sig -> Ctx -> Elem -> Step -> KM (Prf, Elem)
  stepOn sig ctx t step =
    case (step.lic, step.flip, step.sels, step.path) of
      (LUnfoldAll ns, False, [], []) => do
        t' <- unfoldAllK sig ns t
        pure (PDeltaAll ns, t')
      (LUnfoldAll _, _, _, _) => kerr "certificate: an unfold-all step acts at the root, forward"
      -- forward unfold: the spine is spelled at the occurrence
      (LUnfold x es, False, [], path) =>
        kSigLookup sig x >>= \entryX => case entryX of
          Just (SigDef _ _ body _) =>
            wrapAt t path (\b, u => case u of
                SigVar y es' =>
                  if y == x then pure (PDelta x es, substElem body (embed es'))
                    else kerr "certificate: unfold step at a reference to '\{y}', licensed for '\{x}'"
                _ => kerr "certificate: unfold step at a non-reference") 0
          _ => kerr "certificate: unfold step at a non-definition '\{x}'"
      _ => do
        (leaf, _, rN) <- leafOf sig ctx step
        wrapAt t step.path (\b, _ => pure (substPrf leaf (wkN b), substElem rN (wkN b))) 0

  ||| A licence as the kernel reads it — its proof leaf with selectors,
  ||| licence normalization and orientation — and the equation it
  ||| effectively licenses (sides β-joined), in the root context.
  leafOf : Sig -> Ctx -> Step -> KM (Prf, Elem, Elem)
  leafOf sig ctx step = do
    base <- case step.lic of
      LProof p => pure (PRefl p)
      LPath sg k th => pure (PPath sg k th)
      LUnfold x es => pure (PDelta x es)
      LUnfoldAll _ => kerr "certificate: an unfold-all step is forward-only, at the root"
    let leaf0 = foldl (\q, sel => PSel sel q) base step.sels
    (l, r, _) <- kPrfS sig ctx leaf0
    lJ <- kJoinElem sig l
    rJ <- kJoinElem sig r
    (pL, lN) <- chainOn sig ctx lJ (filter (\s => s.onLhs) step.licNorm)
    (pR, rN) <- chainOn sig ctx rJ (filter (\s => not s.onLhs) step.licNorm)
    let leaf = pTrans (pSym pL) (pTrans leaf0 pR)
    pure (if step.flip then (pSym leaf, rN, lN) else (leaf, lN, rN))

  ||| The final as a proof at the rewritten sides.
  finalPrf : Sig -> Ctx -> Final -> Elem -> Elem -> Ty -> KM Prf
  finalPrf sig ctx FBeta l r ty = pure PReflx
  finalPrf sig ctx FProp l r ty = pure PIrrel
  finalPrf sig ctx (FWitness Nothing) l r ty = pure (PQuotWit Nothing)
  finalPrf sig ctx (FWitness (Just c)) l r ty = do
    ty' <- kWhnfT sig ty
    case (l, r, ty') of
      (Class a, Class b, QuotTy _ rel) => do
        relInst <- kJoinElem sig (substElem rel (Ext (Ext Id a) b))
        case relInst of
          Elem.EqTy wl wr wt => PQuotWit . Just <$> toPrfK sig ctx c wl wr wt
          _ => pure (PQuotWit Nothing)
      _ => kerr "certificate: witness final at a non-class equation"
  finalPrf sig ctx (FWitnessPrf w sk) l r ty = pure (PQuotWitPrf w sk)
  finalPrf sig ctx (FInj c) l r ty = do
    ty' <- kWhnfT sig ty
    case (l, r, ty') of
      (Inj1 x, Inj1 y, SumTy a _) => PInj <$> toPrfK sig ctx c x y a
      (Inj2 x, Inj2 y, SumTy _ b) => PInj <$> toPrfK sig ctx c x y b
      _ => kerr "certificate: injection final at a non-matching equation"
  finalPrf sig ctx (FEtaPi c) l r ty = do
    ty' <- kWhnfT sig ty
    case ty' of
      PiTy dom cod =>
        PEtaPi <$> toPrfK sig (ctx :< dom) c
                     (PiApp (substElem l Wk) (CtxVar 0))
                     (PiApp (substElem r Wk) (CtxVar 0)) cod
      _ => kerr "certificate: Π-η final at a non-Π type"
  finalPrf sig ctx (FEtaSigma c1 c2) l r ty = do
    ty' <- kWhnfT sig ty
    case ty' of
      SigmaTy dom cod =>
        [| PEtaSigma (toPrfK sig ctx c1 (SigmaElim1 l) (SigmaElim1 r) dom)
                     (toPrfK sig ctx c2 (SigmaElim2 l) (SigmaElim2 r) (substTy cod (Ext Id (SigmaElim1 l)))) |]
      _ => kerr "certificate: Σ-η final at a non-Σ type"
  finalPrf sig ctx (FPropExt f fs g gs) l r ty = pure (PPropExt f fs g gs)
  finalPrf sig ctx (FPrfCong c) l r ty = PPrfCong <$> toPrfK sig ctx c l r PropTy
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
    (pL, l1) <- chainOn sig ctx l0 (filter (\s => s.onLhs) steps)
    (pR, r1) <- chainOn sig ctx r0 (filter (\s => not s.onLhs) steps)
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
