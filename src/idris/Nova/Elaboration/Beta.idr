module Nova.Elaboration.Beta

-- The ELABORATOR's beta-normaliser. UNTRUSTED: the kernel has its own
-- (Nova.Kernel's kElem/kTy, fuel-bounded inside KM) and never consults
-- this one — NovaPipeline's boundary forbids the kernel believing a
-- normal form computed above it. This module lived under Nova.Kernel.*
-- for a while, which invited exactly the wrong assumption.
--
-- A direct, structurally-recursive beta-reduction algorithm for Ctx/Sub/Ty/
-- Elem/SubNorm, matching every "by definition" (≜) computation
-- rule in docs/NovaFoundation.txt — Π-β, Σ-β₁, Σ-β₂, ℕ-elim-β-Z,
-- ℕ-elim-β-S, quote-elim-β, x-β (signature-variable unfolding), and the
-- El-𝟘/El-𝟙/El-ℕ/El-(→)/El-(⨯)/El-(≡)/El-(/) decoding rules.
--
-- Every function takes the signature Σ as its first argument, since
-- unfolding a SigVar (x-β) needs it — unlike every other rule here, that
-- one can't be decided from the term's own structure alone. Every
-- contraction site (including a SigVar unfold) recurses back through this
-- same module on its result, so a redex exposed only by an earlier
-- contraction (e.g. unfolding x[e˲] to a lambda that's then immediately
-- applied) still gets caught in the same call.
--
-- El-(/) (El (A / R) ≜ El A / R — the relation is an Ω-element and is NOT
-- decoded) is handled the same way as El-(→)/El-(⨯): Elem.QuotTy is the
-- universe code, decoded by betaTy's El case below. Prf has NO decoding
-- rule (Prf ∥A∥ does not reduce to A — that is the point of the squash).

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel.QIIT

import Nova.Profile

import Data.IORef
import Data.SortedMap

%default covering

-- ===== memoised definition normal forms =====
--
-- betaElem (SigVar x es) unfolds a definition and re-normalises its
-- whole body on every mention. At a top-level item the declaration
-- context is empty, so the spine is empty and the substitution is the
-- identity: the call recomputes nf(body) from scratch. A body mentions
-- only earlier entries and names are module-qualified, so nf(body) is
-- stable: with hole support removed, Σ is only ever EXTENDED during a
-- run, so a cached entry is valid for the run's lifetime.
--
-- The unsafePerformIO here is BELOW the trust boundary (see the module
-- header): a stale entry costs completeness, never soundness, since a
-- certificate built on one is rejected at replay. The kernel keeps its
-- own memo in KM's state and shares nothing with this one.

-- ONE allocation for ALL the tables: the Chez backend deduplicates
-- syntactically identical nullary CAFs, so three separate
-- `unsafePerformIO (newIORef empty)` definitions silently share ONE
-- ref (confirmed by exploit: SigEntry inserts reinterpreted as Elem
-- normal forms). Allocating the refs in a single action makes them
-- distinct by construction.
nfCaches : (IORef (SortedMap String Elem), IORef (SortedMap String Ty), IORef (SortedMap String SigEntry))
nfCaches = unsafePerformIO $ do
  e <- newIORef empty
  t <- newIORef empty
  se <- newIORef empty
  pure (e, t, se)

export
betaElemNf : IORef (SortedMap String Elem)
betaElemNf = fst nfCaches

export
betaTyNf : IORef (SortedMap String Ty)
betaTyNf = fst (snd nfCaches)

nfLookup : IORef (SortedMap String a) -> String -> Maybe a
nfLookup ref x = unsafePerformIO $ do
  m <- readIORef ref
  pure (lookup x m)

nfInsert : IORef (SortedMap String a) -> String -> (v : a) -> a
nfInsert ref x v = unsafePerformIO $ do
  modifyIORef ref (insert x v)
  pure v

||| Memoise a lazily-supplied normal form under `x`.
export
nfMemo : IORef (SortedMap String a) -> String -> (Lazy a) -> a
nfMemo ref x v =
  case nfLookup ref x of
    Just w => w
    Nothing => nfInsert ref x (force v)

||| name → entry for the normalisers' SigVar cases: the linear
||| sigLookup scan — measured at ~40% of all execution — is paid once
||| per name instead of once per mention. POSITIVE entries only: a
||| name's entry is stable while Σ only extends (the same monotonicity
||| the nf memos lean on; flips and rebuilds clear this table below,
||| at the same sites). Negatives fall back to the scan and are never
||| cached — a name added later must be found later. Below the trust
||| boundary like everything here: a stale entry costs a rejected
||| certificate, never a wrong acceptance.
export
sigEntryIx : IORef (SortedMap String SigEntry)
sigEntryIx = snd (snd nfCaches)

export
cachedSigLookup : Sig -> String -> Maybe SigEntry
cachedSigLookup sig x =
  case nfLookup sigEntryIx x of
    Just e => Just e
    Nothing => case sigLookup x sig of
                 Just e => Just (nfInsert sigEntryIx x e)
                 Nothing => Nothing


mutual
  ||| e˲, with every element's own beta-redexes rewritten.
  export
  betaSubNorm : Sig -> SubNorm -> SubNorm
  betaSubNorm sig [<] = [<]
  betaSubNorm sig (es :< e) = betaSubNorm sig es :< betaElem sig e

  ||| t, with every Π/Σ/ℕ-elim/quot-elim/x-β redex rewritten.
  export
  betaElem : Sig -> Elem -> Elem
  betaElem sig (CtxVar n)         = CtxVar n
  betaElem sig (ZeroElim t)       = ZeroElim (betaElem sig t)
  betaElem sig OneIntro           = OneIntro
  betaElem sig NatIntro0          = NatIntro0
  betaElem sig (NatIntro1 t)      = NatIntro1 (betaElem sig t)
  betaElem sig (NatElim z s t) =
    let z' = betaElem sig z
        s' = betaElem sig s
    in case betaElem sig t of
         NatIntro0    => z'
         NatIntro1 n  => betaElem sig (substElem s' (Ext (Ext Id n) (NatElim z' s' n)))
         t'           => NatElim z' s' t'
  betaElem sig (PiIntro f)        = PiIntro (betaElem sig f)
  betaElem sig (PiApp f e) =
    let e' = betaElem sig e
    in case betaElem sig f of
         PiIntro g => betaElem sig (substElem g (Ext Id e'))
         f'        => PiApp f' e'
  -- el-let-beta: a let is ALWAYS a redex — let a b ≜ b[id, a, ⋆]
  -- (normal forms contain no let)
  betaElem sig (Let a b) =
    betaElem sig (substElem b (Ext (Ext Id a) Star))
  betaElem sig (SigmaIntro a b)   = SigmaIntro (betaElem sig a) (betaElem sig b)
  betaElem sig (SigmaElim1 t) =
    case betaElem sig t of
      SigmaIntro a _ => a
      t'             => SigmaElim1 t'
  betaElem sig (SigmaElim2 t) =
    case betaElem sig t of
      SigmaIntro _ b => b
      t'             => SigmaElim2 t'
  betaElem sig (Inj1 t)           = Inj1 (betaElem sig t)
  betaElem sig (Inj2 t)           = Inj2 (betaElem sig t)
  betaElem sig (SumElim l r t) =
    let l' = betaElem sig l
        r' = betaElem sig r
    in case betaElem sig t of
         Inj1 a => betaElem sig (substElem l' (Ext Id a))
         Inj2 b => betaElem sig (substElem r' (Ext Id b))
         t'     => SumElim l' r' t'
  betaElem sig Elem.ZeroTy        = Elem.ZeroTy
  betaElem sig Elem.OneTy         = Elem.OneTy
  betaElem sig Elem.NatTy         = Elem.NatTy
  betaElem sig (Elem.PiTy a b)    = Elem.PiTy (betaElem sig a) (betaElem sig b)
  betaElem sig (Elem.SigmaTy a b) = Elem.SigmaTy (betaElem sig a) (betaElem sig b)
  betaElem sig (Elem.SumTy a b)   = Elem.SumTy (betaElem sig a) (betaElem sig b)
  betaElem sig (Elem.EqTy l r t)  = Elem.EqTy (betaElem sig l) (betaElem sig r) (betaTy sig t)
  betaElem sig (QuotTy a r)       = QuotTy (betaElem sig a) (betaElem sig r)
  betaElem sig (SigVar x es) =
    let es' = betaSubNorm sig es
    in case cachedSigLookup sig x of
         Just (SigDef _ _ a _) => betaElem sig (substElem (nfMemo betaElemNf x (betaElem sig a)) (embed es'))
         -- el-sig-decl: a declaration reference is stuck (no -beta)
         Just (SigDecl _ _ _)  => SigVar x es'
         Just _                => assert_total $ idris_crash "betaElem: signature identifier '\{x}' is not a term entry"
         Nothing               => assert_total $ idris_crash "betaElem: signature identifier '\{x}' not found"
  betaElem sig (Class a)          = Class (betaElem sig a)
  betaElem sig (QuotElim f q) =
    case betaElem sig q of
      Class a => betaElem sig (substElem (betaElem sig f) (Ext Id a))
      q'      => QuotElim (betaElem sig f) q'
  -- code-squash-prf: squash is idempotent on props — ∥Prf p∥ ≜ p
  betaElem sig (Squash t)         =
    case betaTy sig t of
      Prf p => p
      t'    => Squash t'
  betaElem sig Star               = Star
  betaElem sig (QSortC sg k es)   = QSortC (betaQSig sig sg) k (betaSubNorm sig es)
  betaElem sig (QCtor sg k es)    = QCtor (betaQSig sig sg) k (betaSubNorm sig es)
  betaElem sig (QElim sg k ms fs es w) =
    let sg' = betaQSig sig sg
        ms' = map (betaTy sig) ms
        fs' = map (betaElem sig) fs
        es' = betaSubNorm sig es
    in case betaElem sig w of
         -- el-qiit-beta: fires only when the two carried signatures are
         -- IDENTICAL after normalization (structural identity, nameless)
         QCtor sgW c theta =>
           if sgW == sg'
             then case qElimBetaRhs sg' ms' fs' c theta of
                    Right rhs => betaElem sig rhs
                    Left err => assert_total $ idris_crash "betaElem: el-qiit-beta on an ill-formed eliminator: \{err}"
             else QElim sg' k ms' fs' es' (QCtor sgW c theta)
         w' => QElim sg' k ms' fs' es' w'
  betaElem sig (Elem.NuTy f)      = Elem.NuTy (betaPoly sig f)
  betaElem sig (Out t) =
    case betaElem sig t of
      -- el-nu-beta: out at a corec head runs the coalgebra one step
      -- and re-wraps the recursive positions (map_𝔽 hᵉˡ f[id, x])
      Corec p a f x => betaElem sig (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
      t'            => Out t'
  betaElem sig (Corec p a f x) =
    Corec (betaPoly sig p) (betaElem sig a) (betaElem sig f) (betaElem sig x)

  ||| The carried polynomial, with every embedded Nova piece normalized.
  export
  betaPoly : Sig -> Poly -> Poly
  betaPoly sig PHole        = PHole
  betaPoly sig (PConst a)   = PConst (betaElem sig a)
  betaPoly sig (PProd f g)  = PProd (betaPoly sig f) (betaPoly sig g)
  betaPoly sig (PSum f g)   = PSum (betaPoly sig f) (betaPoly sig g)
  betaPoly sig (PSigma a f) = PSigma (betaElem sig a) (betaPoly sig f)
  betaPoly sig (PPi a f)    = PPi (betaElem sig a) (betaPoly sig f)

  ||| The carried signature, with every embedded Nova piece normalized.
  export
  betaQTm : Sig -> QTm -> QTm
  betaQTm sig (QVar i)     = QVar i
  betaQTm sig (QAppE f e)  = QAppE (betaQTm sig f) (betaElem sig e)
  betaQTm sig (QAppI f a)  = QAppI (betaQTm sig f) (betaQTm sig a)
  betaQTm sig (QEqC l r u) = QEqC (betaQTm sig l) (betaQTm sig r) (betaQTm sig u)

  export
  betaQTy : Sig -> QTy -> QTy
  betaQTy sig QU           = QU
  betaQTy sig (QEl t)      = QEl (betaQTm sig t)
  betaQTy sig (QPiExt a b) = QPiExt (betaTy sig a) (betaQTy sig b)
  betaQTy sig (QPiInd u b) = QPiInd (betaQTm sig u) (betaQTy sig b)

  export
  betaQSig : Sig -> QSig -> QSig
  betaQSig sig = map (betaQTy sig)

  ||| T, with every beta-redex rewritten: Π/Σ/ℕ-elim/quot-elim/x-β redexes
  ||| inside an El t's argument (via betaElem), type-level x-β (unfolding a
  ||| signature type definition x[e˲] ≜ A[e˲]), plus El-of-universe-code
  ||| decoding — El 𝟘 ≜ 𝟘, El 𝟙 ≜ 𝟙, El ℕ ≜ ℕ, El (A → B) ≜ El A → El B,
  ||| El (A ⨯ B) ≜ El A ⨯ El B, El (a ≡ b ∈ A) ≜ (a ≡ b ∈ El A),
  ||| El (A / R) ≜ El A / R — see the
  ||| El-* rules in docs/NovaFoundation.txt. The decoded result is itself
  ||| recursed into (via betaTy again), since decoding can expose a further
  ||| decodable code (e.g. El of a signature reference that unfolds to 𝟘).
  export
  betaTy : Sig -> Ty -> Ty
  betaTy sig Ty.ZeroTy        = Ty.ZeroTy
  betaTy sig Ty.OneTy         = Ty.OneTy
  betaTy sig Ty.NatTy         = Ty.NatTy
  betaTy sig Ty.UniverseTy    = Ty.UniverseTy
  betaTy sig (Ty.PiTy a b)    = Ty.PiTy (betaTy sig a) (betaTy sig b)
  betaTy sig (Ty.SigmaTy a b) = Ty.SigmaTy (betaTy sig a) (betaTy sig b)
  betaTy sig (Ty.SumTy a b)   = Ty.SumTy (betaTy sig a) (betaTy sig b)
  betaTy sig (El e) =
    case betaElem sig e of
      Elem.ZeroTy      => Ty.ZeroTy
      Elem.OneTy       => Ty.OneTy
      Elem.NatTy       => Ty.NatTy
      Elem.PiTy a b    => betaTy sig (Ty.PiTy (El a) (El b))
      Elem.SigmaTy a b => betaTy sig (Ty.SigmaTy (El a) (El b))
      Elem.SumTy a b   => betaTy sig (Ty.SumTy (El a) (El b))
      QuotTy a r       => betaTy sig (Quotient (El a) r)
      QSortC sg k es   => QSort sg k es      -- ty-el-qiit
      Elem.NuTy f      => Ty.NuTy (betaPoly sig f)   -- ty-el-nu
      e'               => El e'
  betaTy sig PropTy           = PropTy
  betaTy sig (Prf e)          = Prf (betaElem sig e)
  betaTy sig (Quotient a r)   = Quotient (betaTy sig a) (betaElem sig r)
  betaTy sig (Ty.SigVar x es) =
    let es' = betaSubNorm sig es
    in case cachedSigLookup sig x of
         Just (SigTyDef _ _ a) => betaTy sig (substTy (nfMemo betaTyNf x (betaTy sig a)) (embed es'))
         -- ty-sig-decl: a declaration reference is stuck (no -beta)
         Just (SigTyDecl _ _)  => Ty.SigVar x es'
         Just _                => assert_total $ idris_crash "betaTy: signature identifier '\{x}' is not a type entry"
         Nothing               => assert_total $ idris_crash "betaTy: signature identifier '\{x}' not found"
  betaTy sig (QSort sg k es)  = QSort (betaQSig sig sg) k (betaSubNorm sig es)
  betaTy sig (Ty.NuTy f)      = Ty.NuTy (betaPoly sig f)

||| σ, with every element's own beta-redexes rewritten.
export
betaSub : Sig -> Sub -> Sub
betaSub sig Terminal      = Terminal
betaSub sig (Ext s e)     = Ext (betaSub sig s) (betaElem sig e)
betaSub sig (Chain s t)   = Chain (betaSub sig s) (betaSub sig t)
betaSub sig Sub.Id        = Sub.Id
betaSub sig Wk            = Wk



||| Γ, with every type's own beta-redexes rewritten.
export
betaCtx : Sig -> Ctx -> Ctx
betaCtx sig [<]          = [<]
betaCtx sig (rest :< ty) = betaCtx sig rest :< betaTy sig ty

-- ===== the COMPUTATIONAL normaliser (↓ step ½ — tier 1) =====
--
-- The δ-FREE deep normaliser: every ≜ rule EXCEPT signature unfolding
-- (x-β / ty-x-β) — a definition reference is STUCK, like a
-- declaration's. Two sides that join under it are equal "by
-- computation" in the strict sense: Π/Σ/ℕ/⊎/quotient/QIIT/ν
-- eliminations at their introductions, let, El-decoding — with no
-- store, no hypotheses, and no abstraction loss (terms stay in the
-- vocabulary they were written in, and normal forms stay
-- surface-sized: none of the δ-blowup). Signature-free by
-- construction: x-β was the ONLY rule that consulted Σ.

mutual
  export
  compSubNorm : SubNorm -> SubNorm
  compSubNorm [<] = [<]
  compSubNorm (es :< e) = compSubNorm es :< compElem e

  export
  compElem : Elem -> Elem
  compElem (CtxVar n)         = CtxVar n
  compElem (ZeroElim t)       = ZeroElim (compElem t)
  compElem OneIntro           = OneIntro
  compElem NatIntro0          = NatIntro0
  compElem (NatIntro1 t)      = NatIntro1 (compElem t)
  compElem (NatElim z s t) =
    let z' = compElem z
        s' = compElem s
    in case compElem t of
         NatIntro0    => z'
         NatIntro1 n  => compElem (substElem s' (Ext (Ext Id n) (NatElim z' s' n)))
         t'           => NatElim z' s' t'
  compElem (PiIntro f)        = PiIntro (compElem f)
  compElem (PiApp f e) =
    let e' = compElem e
    in case compElem f of
         PiIntro g => compElem (substElem g (Ext Id e'))
         f'        => PiApp f' e'
  compElem (Let a b) =
    compElem (substElem b (Ext (Ext Id a) Star))
  compElem (SigmaIntro a b)   = SigmaIntro (compElem a) (compElem b)
  compElem (SigmaElim1 t) =
    case compElem t of
      SigmaIntro a _ => a
      t'             => SigmaElim1 t'
  compElem (SigmaElim2 t) =
    case compElem t of
      SigmaIntro _ b => b
      t'             => SigmaElim2 t'
  compElem (Inj1 t)           = Inj1 (compElem t)
  compElem (Inj2 t)           = Inj2 (compElem t)
  compElem (SumElim l r t) =
    let l' = compElem l
        r' = compElem r
    in case compElem t of
         Inj1 a => compElem (substElem l' (Ext Id a))
         Inj2 b => compElem (substElem r' (Ext Id b))
         t'     => SumElim l' r' t'
  compElem Elem.ZeroTy        = Elem.ZeroTy
  compElem Elem.OneTy         = Elem.OneTy
  compElem Elem.NatTy         = Elem.NatTy
  compElem (Elem.PiTy a b)    = Elem.PiTy (compElem a) (compElem b)
  compElem (Elem.SigmaTy a b) = Elem.SigmaTy (compElem a) (compElem b)
  compElem (Elem.SumTy a b)   = Elem.SumTy (compElem a) (compElem b)
  compElem (Elem.EqTy l r t)  = Elem.EqTy (compElem l) (compElem r) (compTy t)
  compElem (QuotTy a r)       = QuotTy (compElem a) (compElem r)
  -- x-β omitted: a definition reference is STUCK here, by design
  compElem (SigVar x es)      = SigVar x (compSubNorm es)
  compElem (Class a)          = Class (compElem a)
  compElem (QuotElim f q) =
    case compElem q of
      Class a => compElem (substElem (compElem f) (Ext Id a))
      q'      => QuotElim (compElem f) q'
  compElem (Squash t)         =
    case compTy t of
      Prf p => p
      t'    => Squash t'
  compElem Star               = Star
  compElem (QSortC sg k es)   = QSortC (compQSig sg) k (compSubNorm es)
  compElem (QCtor sg k es)    = QCtor (compQSig sg) k (compSubNorm es)
  compElem (QElim sg k ms fs es w) =
    let sg' = compQSig sg
        ms' = map compTy ms
        fs' = map compElem fs
        es' = compSubNorm es
    in case compElem w of
         QCtor sgW c theta =>
           if sgW == sg'
             then case qElimBetaRhs sg' ms' fs' c theta of
                    Right rhs => compElem rhs
                    Left _ => QElim sg' k ms' fs' es' (QCtor sgW c theta)
             else QElim sg' k ms' fs' es' (QCtor sgW c theta)
         w' => QElim sg' k ms' fs' es' w'
  compElem (Elem.NuTy f)      = Elem.NuTy (compPoly f)
  compElem (Out t) =
    case compElem t of
      Corec p a f x => compElem (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
      t'            => Out t'
  compElem (Corec p a f x) =
    Corec (compPoly p) (compElem a) (compElem f) (compElem x)

  export
  compPoly : Poly -> Poly
  compPoly PHole        = PHole
  compPoly (PConst a)   = PConst (compElem a)
  compPoly (PProd f g)  = PProd (compPoly f) (compPoly g)
  compPoly (PSum f g)   = PSum (compPoly f) (compPoly g)
  compPoly (PSigma a f) = PSigma (compElem a) (compPoly f)
  compPoly (PPi a f)    = PPi (compElem a) (compPoly f)

  export
  compQTm : QTm -> QTm
  compQTm (QVar i)     = QVar i
  compQTm (QAppE f e)  = QAppE (compQTm f) (compElem e)
  compQTm (QAppI f a)  = QAppI (compQTm f) (compQTm a)
  compQTm (QEqC l r u) = QEqC (compQTm l) (compQTm r) (compQTm u)

  export
  compQTy : QTy -> QTy
  compQTy QU           = QU
  compQTy (QEl t)      = QEl (compQTm t)
  compQTy (QPiExt a b) = QPiExt (compTy a) (compQTy b)
  compQTy (QPiInd u b) = QPiInd (compQTm u) (compQTy b)

  export
  compQSig : QSig -> QSig
  compQSig = map compQTy

  export
  compTy : Ty -> Ty
  compTy Ty.ZeroTy        = Ty.ZeroTy
  compTy Ty.OneTy         = Ty.OneTy
  compTy Ty.NatTy         = Ty.NatTy
  compTy Ty.UniverseTy    = Ty.UniverseTy
  compTy (Ty.PiTy a b)    = Ty.PiTy (compTy a) (compTy b)
  compTy (Ty.SigmaTy a b) = Ty.SigmaTy (compTy a) (compTy b)
  compTy (Ty.SumTy a b)   = Ty.SumTy (compTy a) (compTy b)
  compTy (El e) =
    case compElem e of
      Elem.ZeroTy      => Ty.ZeroTy
      Elem.OneTy       => Ty.OneTy
      Elem.NatTy       => Ty.NatTy
      Elem.PiTy a b    => compTy (Ty.PiTy (El a) (El b))
      Elem.SigmaTy a b => compTy (Ty.SigmaTy (El a) (El b))
      Elem.SumTy a b   => compTy (Ty.SumTy (El a) (El b))
      QuotTy a r       => compTy (Quotient (El a) r)
      QSortC sg k es   => QSort sg k es
      Elem.NuTy f      => Ty.NuTy (compPoly f)
      e'               => El e'
  compTy PropTy           = PropTy
  compTy (Prf e)          = Prf (compElem e)
  compTy (Quotient a r)   = Quotient (compTy a) (compElem r)
  -- ty-x-β omitted, like x-β above
  compTy (Ty.SigVar x es) = Ty.SigVar x (compSubNorm es)
  compTy (QSort sg k es)  = QSort (compQSig sg) k (compSubNorm es)
  compTy (Ty.NuTy f)      = Ty.NuTy (compPoly f)

mutual
  ||| WEAK-HEAD normalization, tolerant of open signatures and open
  ||| contexts: contract only at the head, leave every subterm AS
  ||| WRITTEN, and return stuck forms instead of crashing (a scrutinee
  ||| may be a variable or a hole reference here, unlike Nova.Compute's
  ||| closed-term evaluator). Used by the elaborator's decomposition so
  ||| children keep the user's spellings — full betaElem would unfold
  ||| every definition on the way.
  export
  whnfE : Sig -> Elem -> Elem
  whnfE sig (NatElim z s t) =
    case whnfE sig t of
      NatIntro0   => whnfE sig z
      NatIntro1 n => whnfE sig (substElem s (Ext (Ext Id n) (NatElim z s n)))
      t'          => NatElim z s t'
  whnfE sig (PiApp f e) =
    case whnfE sig f of
      PiIntro g => whnfE sig (substElem g (Ext Id e))
      f'        => PiApp f' e
  whnfE sig (Let a b) =
    -- el-let-beta: unconditional — no whnf ever returns a let
    whnfE sig (substElem b (Ext (Ext Id a) Star))
  whnfE sig (SigmaElim1 t) =
    case whnfE sig t of
      SigmaIntro a _ => whnfE sig a
      t'             => SigmaElim1 t'
  whnfE sig (SigmaElim2 t) =
    case whnfE sig t of
      SigmaIntro _ b => whnfE sig b
      t'             => SigmaElim2 t'
  whnfE sig (SumElim l r t) =
    case whnfE sig t of
      Inj1 a => whnfE sig (substElem l (Ext Id a))
      Inj2 b => whnfE sig (substElem r (Ext Id b))
      t'     => SumElim l r t'
  whnfE sig (SigVar x es) =
    case cachedSigLookup sig x of
      Just (SigDef _ _ a _) => whnfE sig (substElem a (embed es))
      _ => SigVar x es
  whnfE sig (QuotElim f q) =
    case whnfE sig q of
      Class a => whnfE sig (substElem f (Ext Id a))
      q'      => QuotElim f q'
  whnfE sig (Squash t) =
    case whnfT sig t of
      Prf p => whnfE sig p       -- code-squash-prf
      t'    => Squash t'
  whnfE sig (QElim sg k ms fs es w) =
    case whnfE sig w of
      QCtor sgW c theta =>
        -- el-qiit-beta demands nf-identical signatures; anything less
        -- than syntactic identity is left to the full-beta fallback
        if sgW == sg
          then case qElimBetaRhs sg ms fs c theta of
                 Right rhs => whnfE sig rhs
                 Left _ => QElim sg k ms fs es (QCtor sgW c theta)
          else QElim sg k ms fs es (QCtor sgW c theta)
      w' => QElim sg k ms fs es w'
  whnfE sig (Out t) =
    case whnfE sig t of
      Corec p a f x => whnfE sig (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
      t'            => Out t'
  whnfE sig e = e

  export
  whnfT : Sig -> Ty -> Ty
  whnfT sig (El e) =
    case whnfE sig e of
      Elem.ZeroTy      => Ty.ZeroTy
      Elem.OneTy       => Ty.OneTy
      Elem.NatTy       => Ty.NatTy
      Elem.PiTy a b    => Ty.PiTy (El a) (El b)
      Elem.SigmaTy a b => Ty.SigmaTy (El a) (El b)
      Elem.SumTy a b   => Ty.SumTy (El a) (El b)
      QuotTy a r       => Quotient (El a) r
      QSortC sg k es   => QSort sg k es    -- ty-el-qiit
      Elem.NuTy f      => Ty.NuTy f        -- ty-el-nu
      e'               => El e'
  whnfT sig (Ty.SigVar x es) =
    case cachedSigLookup sig x of
      Just (SigTyDef _ _ a) => whnfT sig (substTy a (embed es))
      _ => Ty.SigVar x es
  whnfT sig t = t
