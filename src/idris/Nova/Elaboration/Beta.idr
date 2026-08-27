module Nova.Elaboration.Beta

-- The ELABORATOR's COMPUTATIONAL normaliser (comp*): every "by
-- definition" (≜) rule of docs/NovaFoundation.txt EXCEPT signature
-- unfolding (x-β / ty-x-β) — Π-β, Σ-β₁, Σ-β₂, ℕ-elim-β, quot-elim-β,
-- el-qiit-beta, el-nu-beta, let, and code-squash-idem's
-- syntax-directed instances. Definition references are STUCK: δ
-- happens only under the
-- named licenses (see Nova.Elaboration's unfElem/exposeE), never
-- ambiently — the strict-conversion architecture. UNTRUSTED: the
-- kernel has its own normalisers and never consults these.
--
-- (The historical full-δβ normaliser betaElem/betaTy and its def-nf
-- memos lived here until default mode was retired; the kernel's
-- kJoin*/kWhnf* are the surviving trusted-side relatives.)

import Nova.Kernel.Syntax
import Nova.Kernel.Subst
import Nova.Kernel.QIIT

import Nova.Profile

import Data.IORef
import Data.SortedMap

%default covering

-- ===== the Σ-entry name index =====
--
-- name → entry for the normalisers' and exposure's SigVar cases: the
-- linear sigLookup scan — measured at ~40% of all execution once —
-- is paid once per name instead of once per mention. POSITIVE entries
-- only (a name's entry is stable; Σ only extends during a run);
-- negatives fall back to the scan and are never cached. Below the
-- trust boundary. The allocation body is deliberately non-minimal:
-- the Chez backend DEDUPLICATES syntactically identical nullary CAFs
-- (confirmed by exploit — see docs/PerfNotes.md), so this must not
-- textually match any other `unsafePerformIO (newIORef …)`.
export
sigEntryIx : IORef (SortedMap String SigEntry)
sigEntryIx = unsafePerformIO $ do
  ix <- newIORef (the (SortedMap String SigEntry) empty)
  writeIORef ix (the (SortedMap String SigEntry) empty)
  pure ix

||| Clear the name index BETWEEN program runs in one process: the
||| positive-only cache assumes a name's entry is stable, which holds
||| within a run (Σ only extends) but not across runs over DIFFERENT
||| programs — a rename reuses names with changed content, and a stale
||| entry would leak the old spelling into the new run's conversions.
export
clearSigEntryIx : IO ()
clearSigEntryIx = writeIORef sigEntryIx empty

export
cachedSigLookup : Sig -> String -> Maybe SigEntry
cachedSigLookup sig x = unsafePerformIO $ do
  m <- readIORef sigEntryIx
  case lookup x m of
    Just e => pure (Just e)
    Nothing => case sigLookup x sig of
                 Just e => do modifyIORef sigEntryIx (insert x e)
                              pure (Just e)
                 Nothing => pure Nothing

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
  compElem UniverseTy         = UniverseTy
  compElem PropTy             = PropTy
  compElem TopTy              = TopTy
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
      p@(Elem.EqTy _ _ _) => p  -- code-squash-idem instances
      p@(Squash _)        => p
      t'    => Squash t'
  compElem Star               = Star
  compElem (QSort sg k es)   = QSort (compQSig sg) k (compSubNorm es)
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

  ||| One sort: one computational normaliser.
  export
  compTy : Ty -> Ty
  compTy = compElem
