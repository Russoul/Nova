module Nova.Kernel.Beta

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

%default covering

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
  betaElem sig (SigmaIntro a b)   = SigmaIntro (betaElem sig a) (betaElem sig b)
  betaElem sig (SigmaElim1 t) =
    case betaElem sig t of
      SigmaIntro a _ => a
      t'             => SigmaElim1 t'
  betaElem sig (SigmaElim2 t) =
    case betaElem sig t of
      SigmaIntro _ b => b
      t'             => SigmaElim2 t'
  betaElem sig Elem.ZeroTy        = Elem.ZeroTy
  betaElem sig Elem.OneTy         = Elem.OneTy
  betaElem sig Elem.NatTy         = Elem.NatTy
  betaElem sig (Elem.PiTy a b)    = Elem.PiTy (betaElem sig a) (betaElem sig b)
  betaElem sig (Elem.SigmaTy a b) = Elem.SigmaTy (betaElem sig a) (betaElem sig b)
  betaElem sig (Elem.EqTy l r t)  = Elem.EqTy (betaElem sig l) (betaElem sig r) (betaTy sig t)
  betaElem sig (QuotTy a r)       = QuotTy (betaElem sig a) (betaElem sig r)
  betaElem sig (SigVar x es) =
    let es' = betaSubNorm sig es
    in case sigLookup x sig of
         Just (SigDef _ _ a _) => betaElem sig (substElem a (embed es'))
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
  betaTy sig (El e) =
    case betaElem sig e of
      Elem.ZeroTy      => Ty.ZeroTy
      Elem.OneTy       => Ty.OneTy
      Elem.NatTy       => Ty.NatTy
      Elem.PiTy a b    => betaTy sig (Ty.PiTy (El a) (El b))
      Elem.SigmaTy a b => betaTy sig (Ty.SigmaTy (El a) (El b))
      QuotTy a r       => betaTy sig (Quotient (El a) r)
      QSortC sg k es   => QSort sg k es      -- ty-el-qiit
      e'               => El e'
  betaTy sig PropTy           = PropTy
  betaTy sig (Prf e)          = Prf (betaElem sig e)
  betaTy sig (Quotient a r)   = Quotient (betaTy sig a) (betaElem sig r)
  betaTy sig (Ty.SigVar x es) =
    let es' = betaSubNorm sig es
    in case sigLookup x sig of
         Just (SigTyDef _ _ a) => betaTy sig (substTy a (embed es'))
         -- ty-sig-decl: a declaration reference is stuck (no -beta)
         Just (SigTyDecl _ _)  => Ty.SigVar x es'
         Just _                => assert_total $ idris_crash "betaTy: signature identifier '\{x}' is not a type entry"
         Nothing               => assert_total $ idris_crash "betaTy: signature identifier '\{x}' not found"
  betaTy sig (QSort sg k es)  = QSort (betaQSig sig sg) k (betaSubNorm sig es)

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
  whnfE sig (SigmaElim1 t) =
    case whnfE sig t of
      SigmaIntro a _ => whnfE sig a
      t'             => SigmaElim1 t'
  whnfE sig (SigmaElim2 t) =
    case whnfE sig t of
      SigmaIntro _ b => whnfE sig b
      t'             => SigmaElim2 t'
  whnfE sig (SigVar x es) =
    case sigLookup x sig of
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
      QuotTy a r       => Quotient (El a) r
      QSortC sg k es   => QSort sg k es    -- ty-el-qiit
      e'               => El e'
  whnfT sig (Ty.SigVar x es) =
    case sigLookup x sig of
      Just (SigTyDef _ _ a) => whnfT sig (substTy a (embed es))
      _ => Ty.SigVar x es
  whnfT sig t = t
