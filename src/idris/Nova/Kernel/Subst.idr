module Nova.Kernel.Subst

-- A direct, structurally-recursive substitution algorithm for Ty/Elem,
-- matching the "by definition" (≜) substitution equations in
-- docs/NovaFoundation.txt.
--
-- This always fully computes A[σ]/t[σ] in one call — for any Ty/Elem
-- and any concrete σ, since Sub's constructors (Terminal/Ext/Chain/
-- Id/Wk) are always finitely resolvable. It also eagerly resolves any
-- SubstElim already embedded in the input term, so it never leaves a
-- pending substitution behind in its result.
--
-- Argument order matches Syntax.idr's SubstElim (object first, then the
-- substitution): substElem t sigma computes t[σ].
--
-- Composition convention: `Chain s t` prints as "s ∘ t" and behaves like
-- ordinary function composition — s is applied first (to the original
-- term), t second (to s's result) — i.e. `x[Chain s t] = x[s][t]`. This
-- matches the existing (tested) computeSub rule
-- `Chain Wk (Ext sigma _) -> sigma` ("↑ ∘ (σ, e) = σ": weakening
-- immediately cancels a just-added extension) and Syntax.under's
-- `Ext (Chain sigma Wk) (CtxVar 0)` ("σ⁺ = σ ∘ ↑, ☐₀").
--
-- Not wired into the checker yet — this module is standalone.

import Nova.Kernel.Syntax

%default covering

mutual
  ||| e˲[σ]
  export
  substSubNorm : SubNorm -> Sub -> SubNorm
  substSubNorm [<] sigma = [<]
  substSubNorm (es :< e) sigma = substSubNorm es sigma :< substElem e sigma

  ||| ↑ᵏ as a Sub: k-fold weakening composition.
  wkTower : Nat -> Sub
  wkTower Z = Id
  wkTower (S n) = Chain (wkTower n) Wk

  ||| Γ‖ₙ-style variable resolution against a concrete substitution:
  ||| what (☐ₙ)[σ] computes to.
  |||
  ||| Weakening compositions are ACCUMULATED and applied as one shift
  ||| pass at the end: `under`-towers (σ⁺⁺… = … Chain σ ↑) otherwise
  ||| cost one full copy of the resolved payload PER TOWER LAYER —
  ||| x[σ∘↑] ≜ x[σ][↑] applied literally re-traverses the same term k
  ||| times under k binders. Extensionally identical to the literal
  ||| equations (x[σ][↑ᵏ] computed in one pass), measured at >50% of
  ||| all execution on the ℝ corpus before the change.
  export
  substVar : Nat -> Sub -> Elem
  substVar n sigma = go n sigma Z
   where
    ||| shift k t = t[↑ᵏ], one traversal (the tower has no Ext
    ||| payloads, so resolving its variables allocates nothing).
    shift : Nat -> Elem -> Elem
    shift Z t = t
    shift k t = substElem t (wkTower k)

    go : Nat -> Sub -> (pending : Nat) -> Elem
    -- Terminal's codomain is ε, which has no variables, so ☐ₙ can never be
    -- well-typed there — crash loudly instead of fabricating a result.
    go n     Terminal    k = assert_total $ idris_crash "substVar: ill-typed ☐\{show n} against · (empty codomain)"
    go n     Id          k = CtxVar (n + k)
    go n     Wk          k = CtxVar (S (n + k))
    go Z     (Ext sigma t) k = shift k t
    go (S n) (Ext sigma t) k = go n sigma k
    go n     (Chain s Wk) k = go n s (S k)
    go n     (Chain s Id) k = go n s k
    go n     (Chain s t) k = shift k (substElem (go n s Z) t)

  ||| t[σ]
  export
  substElem : Elem -> Sub -> Elem
  -- x[id] ≜ x, and a term is a pure tree (no pending substitutions),
  -- so the identity acts as the identity without a traversal
  substElem t                  Id    = t
  substElem (CtxVar n)         sigma = substVar n sigma
  substElem (ZeroElim t)       sigma = ZeroElim (substElem t sigma)
  substElem OneIntro           sigma = OneIntro
  substElem NatIntro0          sigma = NatIntro0
  substElem (NatIntro1 t)      sigma = NatIntro1 (substElem t sigma)
  substElem (NatElim z s t)    sigma = NatElim (substElem z sigma) (substElem s (under (under sigma))) (substElem t sigma)
  substElem (PiIntro f)        sigma = PiIntro (substElem f (under sigma))
  substElem (PiApp f e)        sigma = PiApp (substElem f sigma) (substElem e sigma)
  substElem (Let a b)          sigma = Let (substElem a sigma) (substElem b (under (under sigma)))
  substElem (SigmaIntro a b)   sigma = SigmaIntro (substElem a sigma) (substElem b sigma)
  substElem (SigmaElim1 t)     sigma = SigmaElim1 (substElem t sigma)
  substElem (SigmaElim2 t)     sigma = SigmaElim2 (substElem t sigma)
  substElem (Inj1 t)           sigma = Inj1 (substElem t sigma)
  substElem (Inj2 t)           sigma = Inj2 (substElem t sigma)
  substElem (SumElim l r t)    sigma = SumElim (substElem l (under sigma)) (substElem r (under sigma)) (substElem t sigma)
  substElem Elem.ZeroTy        sigma = Elem.ZeroTy
  substElem Elem.OneTy         sigma = Elem.OneTy
  substElem Elem.NatTy         sigma = Elem.NatTy
  substElem (Elem.PiTy a b)    sigma = Elem.PiTy (substElem a sigma) (substElem b (under sigma))
  substElem (Elem.SigmaTy a b) sigma = Elem.SigmaTy (substElem a sigma) (substElem b (under sigma))
  substElem (Elem.SumTy a b)   sigma = Elem.SumTy (substElem a sigma) (substElem b sigma)
  substElem (Elem.EqTy l r t)  sigma = Elem.EqTy (substElem l sigma) (substElem r sigma) (substTy t sigma)
  substElem (QuotTy a r)       sigma = QuotTy (substElem a sigma) (substElem r (under (under sigma)))
  substElem (SigVar x es)      sigma = SigVar x (substSubNorm es sigma)
  substElem (Class a)          sigma = Class (substElem a sigma)
  substElem (QuotElim f q)     sigma = QuotElim (substElem f (under sigma)) (substElem q sigma)
  substElem (Squash t)         sigma = Squash (substTy t sigma)
  substElem Star               sigma = Star
  substElem (QSortC sg k es)   sigma = QSortC (substQSig sg sigma) k (substSubNorm es sigma)
  substElem (QCtor sg k es)    sigma = QCtor (substQSig sg sigma) k (substSubNorm es sigma)
  substElem (QElim sg k ms fs es w) sigma =
    QElim (substQSig sg sigma) k
      (substMotives sg ms sigma) (map (\f => substElem f sigma) fs)
      (substSubNorm es sigma) (substElem w sigma)
  substElem (Elem.NuTy f)      sigma = Elem.NuTy (substPoly f sigma)
  substElem (Out t)            sigma = Out (substElem t sigma)
  substElem (Corec p a f x)    sigma =
    Corec (substPoly p sigma) (substElem a sigma) (substElem f (under sigma)) (substElem x sigma)

  ||| Motive i lives over Γ·⌊𝔎ᵢ⌋ᵗ ▷ 𝒮.kᵢ δ — lift σ once per index
  ||| binder plus once for the eliminee.
  substMotives : QSig -> List Ty -> Sub -> List Ty
  substMotives sg ms sigma = go (qPositions QKSort sg) ms
   where
    underN : Nat -> Sub -> Sub
    underN Z s = s
    underN (S n) s = under (underN n s)
    go : List Nat -> List Ty -> List Ty
    go _ [] = []
    go [] (m :: rest) = m :: rest   -- ill-formed ℰ; substitution stays total
    go (k :: ks) (m :: rest) = substTy m (underN (S (qArityLen sg k)) sigma) :: go ks rest

  ||| Nova substitution THROUGH ToS syntax: σ acts on every embedded
  ||| Nova piece, lifted (under) at EXTERNAL binders only — ToS
  ||| variables are inert (⬡ᵢ[σ] ≜ ⬡ᵢ; the two calculi act on disjoint
  ||| namespaces).
  export
  substQTm : QTm -> Sub -> QTm
  substQTm (QVar i)     sigma = QVar i
  substQTm (QAppE f e)  sigma = QAppE (substQTm f sigma) (substElem e sigma)
  substQTm (QAppI f a)  sigma = QAppI (substQTm f sigma) (substQTm a sigma)
  substQTm (QEqC l r u) sigma = QEqC (substQTm l sigma) (substQTm r sigma) (substQTm u sigma)

  export
  substQTy : QTy -> Sub -> QTy
  substQTy QU            sigma = QU
  substQTy (QEl t)       sigma = QEl (substQTm t sigma)
  substQTy (QPiExt a b)  sigma = QPiExt (substTy a sigma) (substQTy b (under sigma))
  substQTy (QPiInd u b)  sigma = QPiInd (substQTm u sigma) (substQTy b sigma)

  export
  substQSig : QSig -> Sub -> QSig
  substQSig sg sigma = map (\t => substQTy t sigma) sg

  ||| 𝔽[σ] — σ on the embedded Nova pieces, lifted under the binding
  ||| formers; the hole is inert.
  export
  substPoly : Poly -> Sub -> Poly
  substPoly PHole        sigma = PHole
  substPoly (PConst a)   sigma = PConst (substElem a sigma)
  substPoly (PProd f g)  sigma = PProd (substPoly f sigma) (substPoly g sigma)
  substPoly (PSum f g)   sigma = PSum (substPoly f sigma) (substPoly g sigma)
  substPoly (PSigma a f) sigma = PSigma (substElem a sigma) (substPoly f (under sigma))
  substPoly (PPi a f)    sigma = PPi (substElem a sigma) (substPoly f (under sigma))

  ||| T[σ]
  export
  substTy : Ty -> Sub -> Ty
  -- A[id] ≜ A, as at substElem
  substTy t                     Id    = t
  substTy Ty.ZeroTy             sigma = Ty.ZeroTy
  substTy Ty.OneTy              sigma = Ty.OneTy
  substTy Ty.NatTy              sigma = Ty.NatTy
  substTy Ty.UniverseTy         sigma = Ty.UniverseTy
  substTy (Ty.PiTy a b)         sigma = Ty.PiTy (substTy a sigma) (substTy b (under sigma))
  substTy (Ty.SigmaTy a b)      sigma = Ty.SigmaTy (substTy a sigma) (substTy b (under sigma))
  substTy (Ty.SumTy a b)        sigma = Ty.SumTy (substTy a sigma) (substTy b sigma)
  substTy (El e)                sigma = El (substElem e sigma)
  substTy PropTy                sigma = PropTy
  substTy (Prf e)               sigma = Prf (substElem e sigma)
  substTy (Quotient a r)        sigma = Quotient (substTy a sigma) (substElem r (under (under sigma)))
  substTy (Ty.SigVar x es)      sigma = Ty.SigVar x (substSubNorm es sigma)
  substTy (QSort sg k es)       sigma = QSort (substQSig sg sigma) k (substSubNorm es sigma)
  substTy (Ty.NuTy f)           sigma = Ty.NuTy (substPoly f sigma)



export
embed : SubNorm -> Sub
embed [<] = Terminal
embed (es :< e) = Ext (embed es) e

-- ===== Strengthening (partial inverse of weakening by ↑) =====
--
-- strengthenXxx d x undoes one weakening step: it succeeds exactly when x
-- never references the variable at de Bruijn depth d (i.e. x is in the
-- image of ↑ under d local binders), returning x with every free index
-- above d decremented. Binder bookkeeping mirrors substXxx exactly. Used
-- by the elaborator's candidate canonicalization; call with d = 0.
--
-- NOTE: strengthening is a raw syntactic operation — index arithmetic
-- only. Its output is NOT necessarily well-formed (nothing here consults
-- a context or the signature), and success does NOT mean the input was
-- derivable one binder up: it only means the input is syntactically in
-- the image of ↑. Callers must never treat a strengthened result as a
-- judgement — the elaborator uses it only to canonicalize candidate
-- patterns, and anything it produces is re-established by the kernel.

mutual
  export
  strengthenElem : (depth : Nat) -> Elem -> Maybe Elem
  strengthenElem d (CtxVar n) =
    if n < d then Just (CtxVar n)
    else if n == d then Nothing
    else Just (CtxVar (minus n 1))
  strengthenElem d (ZeroElim t)       = ZeroElim <$> strengthenElem d t
  strengthenElem d OneIntro           = Just OneIntro
  strengthenElem d NatIntro0          = Just NatIntro0
  strengthenElem d (NatIntro1 t)      = NatIntro1 <$> strengthenElem d t
  strengthenElem d (NatElim z s t)    = NatElim <$> strengthenElem d z <*> strengthenElem (2 + d) s <*> strengthenElem d t
  strengthenElem d (PiIntro f)        = PiIntro <$> strengthenElem (1 + d) f
  strengthenElem d (PiApp f e)        = PiApp <$> strengthenElem d f <*> strengthenElem d e
  strengthenElem d (Let a b)          = Let <$> strengthenElem d a <*> strengthenElem (2 + d) b
  strengthenElem d (SigmaIntro a b)   = SigmaIntro <$> strengthenElem d a <*> strengthenElem d b
  strengthenElem d (SigmaElim1 t)     = SigmaElim1 <$> strengthenElem d t
  strengthenElem d (SigmaElim2 t)     = SigmaElim2 <$> strengthenElem d t
  strengthenElem d (Inj1 t)           = Inj1 <$> strengthenElem d t
  strengthenElem d (Inj2 t)           = Inj2 <$> strengthenElem d t
  strengthenElem d (SumElim l r t)    = SumElim <$> strengthenElem (1 + d) l <*> strengthenElem (1 + d) r <*> strengthenElem d t
  strengthenElem d Elem.ZeroTy        = Just Elem.ZeroTy
  strengthenElem d Elem.OneTy         = Just Elem.OneTy
  strengthenElem d Elem.NatTy         = Just Elem.NatTy
  strengthenElem d (Elem.PiTy a b)    = Elem.PiTy <$> strengthenElem d a <*> strengthenElem (1 + d) b
  strengthenElem d (Elem.SigmaTy a b) = Elem.SigmaTy <$> strengthenElem d a <*> strengthenElem (1 + d) b
  strengthenElem d (Elem.SumTy a b)   = Elem.SumTy <$> strengthenElem d a <*> strengthenElem d b
  strengthenElem d (Elem.EqTy l r t)  = Elem.EqTy <$> strengthenElem d l <*> strengthenElem d r <*> strengthenTy d t
  strengthenElem d (QuotTy a r)       = QuotTy <$> strengthenElem d a <*> strengthenElem (2 + d) r
  strengthenElem d (SigVar x es)      = SigVar x <$> strengthenSubNorm d es
  strengthenElem d (Class a)          = Class <$> strengthenElem d a
  strengthenElem d (QuotElim f q)     = QuotElim <$> strengthenElem (1 + d) f <*> strengthenElem d q
  strengthenElem d (Squash t)         = Squash <$> strengthenTy d t
  strengthenElem d Star               = Just Star
  strengthenElem d (QSortC sg k es)   = QSortC <$> strengthenQSig d sg <*> Just k <*> strengthenSubNorm d es
  strengthenElem d (QCtor sg k es)    = QCtor <$> strengthenQSig d sg <*> Just k <*> strengthenSubNorm d es
  strengthenElem d (QElim sg k ms fs es w) =
    QElim <$> strengthenQSig d sg <*> Just k
          <*> goMs (qPositions QKSort sg) ms
          <*> traverse (strengthenElem d) fs
          <*> strengthenSubNorm d es <*> strengthenElem d w
   where
    goMs : List Nat -> List Ty -> Maybe (List Ty)
    goMs _ [] = Just []
    goMs [] (m :: rest) = Nothing
    goMs (kk :: ks) (m :: rest) =
      [| strengthenTy (d + S (qArityLen sg kk)) m :: goMs ks rest |]
  strengthenElem d (Elem.NuTy f)      = Elem.NuTy <$> strengthenPoly d f
  strengthenElem d (Out t)            = Out <$> strengthenElem d t
  strengthenElem d (Corec p a f x)    =
    Corec <$> strengthenPoly d p <*> strengthenElem d a
          <*> strengthenElem (1 + d) f <*> strengthenElem d x

  export
  strengthenQTm : (depth : Nat) -> QTm -> Maybe QTm
  strengthenQTm d (QVar i)     = Just (QVar i)
  strengthenQTm d (QAppE f e)  = QAppE <$> strengthenQTm d f <*> strengthenElem d e
  strengthenQTm d (QAppI f a)  = QAppI <$> strengthenQTm d f <*> strengthenQTm d a
  strengthenQTm d (QEqC l r u) = QEqC <$> strengthenQTm d l <*> strengthenQTm d r <*> strengthenQTm d u

  export
  strengthenQTy : (depth : Nat) -> QTy -> Maybe QTy
  strengthenQTy d QU           = Just QU
  strengthenQTy d (QEl t)      = QEl <$> strengthenQTm d t
  strengthenQTy d (QPiExt a b) = QPiExt <$> strengthenTy d a <*> strengthenQTy (1 + d) b
  strengthenQTy d (QPiInd u b) = QPiInd <$> strengthenQTm d u <*> strengthenQTy d b

  export
  strengthenQSig : (depth : Nat) -> QSig -> Maybe QSig
  strengthenQSig d = traverse (strengthenQTy d)

  export
  strengthenPoly : (depth : Nat) -> Poly -> Maybe Poly
  strengthenPoly d PHole        = Just PHole
  strengthenPoly d (PConst a)   = PConst <$> strengthenElem d a
  strengthenPoly d (PProd f g)  = PProd <$> strengthenPoly d f <*> strengthenPoly d g
  strengthenPoly d (PSum f g)   = PSum <$> strengthenPoly d f <*> strengthenPoly d g
  strengthenPoly d (PSigma a f) = PSigma <$> strengthenElem d a <*> strengthenPoly (1 + d) f
  strengthenPoly d (PPi a f)    = PPi <$> strengthenElem d a <*> strengthenPoly (1 + d) f

  export
  strengthenSubNorm : (depth : Nat) -> SubNorm -> Maybe SubNorm
  strengthenSubNorm d [<] = Just [<]
  strengthenSubNorm d (es :< e) = (:<) <$> strengthenSubNorm d es <*> strengthenElem d e

  export
  strengthenTy : (depth : Nat) -> Ty -> Maybe Ty
  strengthenTy d Ty.ZeroTy         = Just Ty.ZeroTy
  strengthenTy d Ty.OneTy          = Just Ty.OneTy
  strengthenTy d Ty.NatTy          = Just Ty.NatTy
  strengthenTy d Ty.UniverseTy     = Just Ty.UniverseTy
  strengthenTy d (Ty.PiTy a b)     = Ty.PiTy <$> strengthenTy d a <*> strengthenTy (1 + d) b
  strengthenTy d (Ty.SigmaTy a b)  = Ty.SigmaTy <$> strengthenTy d a <*> strengthenTy (1 + d) b
  strengthenTy d (Ty.SumTy a b)    = Ty.SumTy <$> strengthenTy d a <*> strengthenTy d b
  strengthenTy d (El e)            = El <$> strengthenElem d e
  strengthenTy d PropTy            = Just PropTy
  strengthenTy d (Prf e)           = Prf <$> strengthenElem d e
  strengthenTy d (Quotient a r)    = Quotient <$> strengthenTy d a <*> strengthenElem (2 + d) r
  strengthenTy d (Ty.SigVar x es)  = Ty.SigVar x <$> strengthenSubNorm d es
  strengthenTy d (QSort sg k es)   = QSort <$> strengthenQSig d sg <*> Just k <*> strengthenSubNorm d es
  strengthenTy d (Ty.NuTy f)       = Ty.NuTy <$> strengthenPoly d f

||| Only surface-shaped substitutions (flat Ext/Terminal element lists)
||| strengthen; Id/Wk/Chain are index-sensitive and never appear in
||| queries, so they conservatively fail.
export
strengthenSub : (depth : Nat) -> Sub -> Maybe Sub
strengthenSub d Terminal  = Just Terminal
strengthenSub d (Ext s e) = Ext <$> strengthenSub d s <*> strengthenElem d e
strengthenSub d _         = Nothing



||| σ elementwise-weakened by ↑ — how the same (surface, Ext/Terminal)
||| substitution is spelled one binder up in its domain (σ ∘ ↑, by the
||| extension-postcomposition rule). Id/Wk/Chain are unreachable here
||| (strengthenSub never produces them) — crash loudly rather than
||| fabricate a result.
export
weakenSub : Sub -> Sub
weakenSub Terminal  = Terminal
weakenSub (Ext s e) = Ext (weakenSub s) (substElem e Wk)
weakenSub s         = assert_total $ idris_crash "weakenSub: non-surface substitution"


-- ===== Coinductive meta-operations (Foundation, coinductive section) =====

||| ⌊𝔽⌋(c) — the code with the hole filled by c (a code over the same
||| context as 𝔽). c weakens under the binding formers; the non-binding
||| product's second component crosses code-sigma's binder, so it
||| weakens too.
export covering
reflectPoly : Poly -> Elem -> Elem
reflectPoly PHole        c = c
reflectPoly (PConst a)   c = a
reflectPoly (PProd f g)  c =
  Elem.SigmaTy (reflectPoly f c) (substElem (reflectPoly g c) Wk)
reflectPoly (PSum f g)   c = Elem.SumTy (reflectPoly f c) (reflectPoly g c)
reflectPoly (PSigma a f) c = Elem.SigmaTy a (reflectPoly f (substElem c Wk))
reflectPoly (PPi a f)    c = Elem.PiTy a (reflectPoly f (substElem c Wk))

||| map_𝔽 g x — the functorial action, applied: an element of
||| El ⌊𝔽⌋(c₀) rebuilt with g : El c₀ → El c₁ at the hole positions.
||| g and x weaken under the binders the clauses cross; at the binding
||| formers the body polynomial is INSTANTIATED (PSigma: at the first
||| component; PPi: at the freshly bound argument).
export covering
mapPoly : Poly -> (g : Elem) -> (x : Elem) -> Elem
mapPoly PHole        g x = PiApp g x
mapPoly (PConst a)   g x = x
mapPoly (PProd f h)  g x =
  SigmaIntro (mapPoly f g (SigmaElim1 x)) (mapPoly h g (SigmaElim2 x))
mapPoly (PSum f h)   g x =
  SumElim (Inj1 (mapPoly (substPoly f Wk) (substElem g Wk) (CtxVar 0)))
          (Inj2 (mapPoly (substPoly h Wk) (substElem g Wk) (CtxVar 0)))
          x
mapPoly (PSigma a f) g x =
  SigmaIntro (SigmaElim1 x)
             (mapPoly (substPoly f (Ext Id (SigmaElim1 x))) g (SigmaElim2 x))
mapPoly (PPi a f)    g x =
  PiIntro (mapPoly f (substElem g Wk) (PiApp (substElem x Wk) (CtxVar 0)))

||| hᵉˡ ≜ λ (corec 𝔽 a f[↑] ☐₀) — the corecursor as a function term
||| (el-nu-beta's re-wrapper).
export covering
corecFun : Poly -> (a : Elem) -> (f : Elem) -> Elem
corecFun p a f =
  PiIntro (Corec (substPoly p Wk) (substElem a Wk) (substElem f (under Wk)) (CtxVar 0))

||| lift_𝔽(R) u v — the RELATOR: the relation lifting of a polynomial
||| (Foundation, el-nu-coind). R is an Ω-valued OPEN term with two
||| bound variables (Γ ▷ ν𝔽 ▷ (ν𝔽)[↑], ☐₁ the left side, ☐₀ the
||| right); u and v are elements of El ⌊𝔽⌋(c)'s decoding in the
||| ambient context; the result is an Ω-element there. One clause per
||| former: the hole instantiates R, constants compare by ≡, products
||| are Ω-conjunctions (squashed Σ of Prfs), sums match tags by a
||| dependent ⊎-elim at motive Ω (⊥ off the diagonal, definitional
||| collapse on it), the dependent pair binds the first-component
||| equation so the instances are ≐ by reflection (no transport), and
||| exponents lift pointwise. R's BASE weakens under every binder the
||| clauses cross (its own two binders lift over it).
export covering
liftPoly : Poly -> (r : Elem) -> (u : Elem) -> (v : Elem) -> Elem
liftPoly PHole        r u v = substElem r (Ext (Ext Id u) v)
liftPoly (PConst a)   r u v = Elem.EqTy u v (El a)
liftPoly (PProd f g)  r u v =
  Squash (Ty.SigmaTy (Prf (liftPoly f r (SigmaElim1 u) (SigmaElim1 v)))
                     (substTy (Prf (liftPoly g r (SigmaElim2 u) (SigmaElim2 v))) Wk))
liftPoly (PSum f g)   r u v =
  SumElim
    (SumElim (liftPoly f (wk2base r) (CtxVar 1) (CtxVar 0))
             (Squash Ty.ZeroTy)
             (substElem v Wk))
    (SumElim (Squash Ty.ZeroTy)
             (liftPoly g (wk2base r) (CtxVar 1) (CtxVar 0))
             (substElem v Wk))
    u
 where
  wk2base : Elem -> Elem
  wk2base e = substElem (substElem e (under (under Wk))) (under (under Wk))
liftPoly (PSigma a f) r u v =
  Squash (Ty.SigmaTy
    (Prf (Elem.EqTy (SigmaElim1 u) (SigmaElim1 v) (El a)))
    (Prf (liftPoly (substPoly (substPoly f (Ext Id (SigmaElim1 u))) Wk)
                   (substElem r (under (under Wk)))
                   (substElem (SigmaElim2 u) Wk)
                   (substElem (SigmaElim2 v) Wk))))
liftPoly (PPi a f)    r u v =
  Squash (Ty.PiTy (El a)
    (Prf (liftPoly f
                   (substElem r (under (under Wk)))
                   (PiApp (substElem u Wk) (CtxVar 0))
                   (PiApp (substElem v Wk) (CtxVar 0)))))
