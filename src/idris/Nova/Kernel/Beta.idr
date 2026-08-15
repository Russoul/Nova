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

import Data.List
import Data.SnocList
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
    in case sigLookup x sig of
         Just (SigTyDef _ _ a) => betaTy sig (substTy a (embed es'))
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
    case sigLookup x sig of
      Just (SigTyDef _ _ a) => whnfT sig (substTy a (embed es))
      _ => Ty.SigVar x es
  whnfT sig t = t


-- ===== SINGLE-STEP CONTRACTION AT A PATH (the beta-at primitive;
-- docs/NovaDerivations.txt, the nf oracle section) =====
--
-- One ≜ contraction, HEAD position: exactly one clause per ≜ rule,
-- read side by side with Foundation's ≜ section. Nothing when the
-- head is not a redex — the caller (a beta-at derivation node, or
-- the engine's positionalizer) owns the position choice.

export
step1E : Sig -> Elem -> Maybe Elem
step1E sig (PiApp (PiIntro g) e) = Just (substElem g (Ext Id e))
step1E sig (Let a b) = Just (substElem b (Ext (Ext Id a) Star))
step1E sig (NatElim z s NatIntro0) = Just z
step1E sig (NatElim z s (NatIntro1 n)) =
  Just (substElem s (Ext (Ext Id n) (NatElim z s n)))
step1E sig (SigmaElim1 (SigmaIntro a _)) = Just a
step1E sig (SigmaElim2 (SigmaIntro _ b)) = Just b
step1E sig (SumElim l r (Inj1 a)) = Just (substElem l (Ext Id a))
step1E sig (SumElim l r (Inj2 b)) = Just (substElem r (Ext Id b))
step1E sig (Elem.SigVar x es) =
  case sigLookup x sig of
    Just (SigDef _ _ a _) => Just (substElem a (embed es))
    _ => Nothing
step1E sig (QuotElim f (Class a)) = Just (substElem f (Ext Id a))
step1E sig (Squash (Prf p)) = Just p
step1E sig (QElim sg k ms fs es (QCtor sgW c theta)) =
  if sgW == sg
    then case qElimBetaRhs sg ms fs c theta of
           Right rhs => Just rhs
           Left _ => Nothing
    else Nothing
step1E sig (Out (Corec p a f x)) =
  Just (mapPoly p (corecFun p a f) (substElem f (Ext Id x)))
step1E sig _ = Nothing

export
step1T : Sig -> Ty -> Maybe Ty
step1T sig (El Elem.ZeroTy) = Just Ty.ZeroTy
step1T sig (El Elem.OneTy) = Just Ty.OneTy
step1T sig (El Elem.NatTy) = Just Ty.NatTy
step1T sig (El (Elem.PiTy a b)) = Just (Ty.PiTy (El a) (El b))
step1T sig (El (Elem.SigmaTy a b)) = Just (Ty.SigmaTy (El a) (El b))
step1T sig (El (Elem.SumTy a b)) = Just (Ty.SumTy (El a) (El b))
step1T sig (El (QuotTy a r)) = Just (Quotient (El a) r)
step1T sig (El (QSortC sg k es)) = Just (QSort sg k es)
step1T sig (El (Elem.NuTy f)) = Just (Ty.NuTy f)
step1T sig (Ty.SigVar x es) =
  case sigLookup x sig of
    Just (SigTyDef _ _ a) => Just (substTy a (embed es))
    _ => Nothing
step1T sig _ = Nothing

-- The path descent: pure spelling surgery, child indices exactly the
-- kernel's table (docs/NovaKernel.txt path grammar; binders cross
-- silently — contraction carries no license to weaken).
mutual
  export
  contractAtE : Sig -> List Nat -> Elem -> Maybe Elem
  contractAtE sig [] e = step1E sig e
  contractAtE sig (i :: p) e =
    case (e, i) of
      (ZeroElim t, 0) => ZeroElim <$> contractAtE sig p t
      (NatIntro1 t, 0) => NatIntro1 <$> contractAtE sig p t
      (NatElim z s t, 0) => (\z' => NatElim z' s t) <$> contractAtE sig p z
      (NatElim z s t, 1) => (\s' => NatElim z s' t) <$> contractAtE sig p s
      (NatElim z s t, 2) => NatElim z s <$> contractAtE sig p t
      (PiIntro f, 0) => PiIntro <$> contractAtE sig p f
      (PiApp f e2, 0) => (\f' => PiApp f' e2) <$> contractAtE sig p f
      (PiApp f e2, 1) => PiApp f <$> contractAtE sig p e2
      (Let a b, 0) => (\a' => Let a' b) <$> contractAtE sig p a
      (Let a b, 1) => Let a <$> contractAtE sig p b
      (SigmaIntro a b, 0) => (\a' => SigmaIntro a' b) <$> contractAtE sig p a
      (SigmaIntro a b, 1) => SigmaIntro a <$> contractAtE sig p b
      (SigmaElim1 t, 0) => SigmaElim1 <$> contractAtE sig p t
      (SigmaElim2 t, 0) => SigmaElim2 <$> contractAtE sig p t
      (Inj1 t, 0) => Inj1 <$> contractAtE sig p t
      (Inj2 t, 0) => Inj2 <$> contractAtE sig p t
      (SumElim l r t, 0) => (\l' => SumElim l' r t) <$> contractAtE sig p l
      (SumElim l r t, 1) => (\r' => SumElim l r' t) <$> contractAtE sig p r
      (SumElim l r t, 2) => SumElim l r <$> contractAtE sig p t
      (Elem.PiTy a b, 0) => (\a' => Elem.PiTy a' b) <$> contractAtE sig p a
      (Elem.PiTy a b, 1) => Elem.PiTy a <$> contractAtE sig p b
      (Elem.SigmaTy a b, 0) => (\a' => Elem.SigmaTy a' b) <$> contractAtE sig p a
      (Elem.SigmaTy a b, 1) => Elem.SigmaTy a <$> contractAtE sig p b
      (Elem.SumTy a b, 0) => (\a' => Elem.SumTy a' b) <$> contractAtE sig p a
      (Elem.SumTy a b, 1) => Elem.SumTy a <$> contractAtE sig p b
      (Elem.EqTy l r t, 0) => (\l' => Elem.EqTy l' r t) <$> contractAtE sig p l
      (Elem.EqTy l r t, 1) => (\r' => Elem.EqTy l r' t) <$> contractAtE sig p r
      (Elem.EqTy l r t, 2) => Elem.EqTy l r <$> contractAtT sig p t
      (QuotTy a r, 0) => (\a' => QuotTy a' r) <$> contractAtE sig p a
      (QuotTy a r, 1) => QuotTy a <$> contractAtE sig p r
      (Elem.SigVar x es, _) =>
        Elem.SigVar x <$> contractSpine sig i p es
      (Class a, 0) => Class <$> contractAtE sig p a
      (QuotElim f q, 0) => (\f' => QuotElim f' q) <$> contractAtE sig p f
      (QuotElim f q, 1) => QuotElim f <$> contractAtE sig p q
      (Squash t, 0) => Squash <$> contractAtT sig p t
      (QSortC sg k es, _) =>
        (\es' => QSortC sg k es') <$> contractSpine sig i p es
      (QCtor sg k es, _) =>
        (\es' => QCtor sg k es') <$> contractSpine sig i p es
      (QElim sg k ms fs es w, _) =>
        if i == length (toList es)
          then QElim sg k ms fs es <$> contractAtE sig p w
          else (\es' => QElim sg k ms fs es' w) <$> contractSpine sig i p es
      (Out t, 0) => Out <$> contractAtE sig p t
      (Corec pf a f x, 0) => (\a' => Corec pf a' f x) <$> contractAtE sig p a
      (Corec pf a f x, 1) => (\f' => Corec pf a f' x) <$> contractAtE sig p f
      (Corec pf a f x, 2) => Corec pf a f <$> contractAtE sig p x
      _ => Nothing

  export
  contractAtT : Sig -> List Nat -> Ty -> Maybe Ty
  contractAtT sig [] t = step1T sig t
  contractAtT sig (i :: p) t =
    case (t, i) of
      (Ty.PiTy a b, 0) => (\a' => Ty.PiTy a' b) <$> contractAtT sig p a
      (Ty.PiTy a b, 1) => Ty.PiTy a <$> contractAtT sig p b
      (Ty.SigmaTy a b, 0) => (\a' => Ty.SigmaTy a' b) <$> contractAtT sig p a
      (Ty.SigmaTy a b, 1) => Ty.SigmaTy a <$> contractAtT sig p b
      (Ty.SumTy a b, 0) => (\a' => Ty.SumTy a' b) <$> contractAtT sig p a
      (Ty.SumTy a b, 1) => Ty.SumTy a <$> contractAtT sig p b
      (El e, 0) => El <$> contractAtE sig p e
      (Prf e, 0) => Prf <$> contractAtE sig p e
      (Quotient a r, 0) => (\a' => Quotient a' r) <$> contractAtT sig p a
      (Quotient a r, 1) => Quotient a <$> contractAtE sig p r
      (Ty.SigVar x es, _) =>
        Ty.SigVar x <$> contractSpine sig i p es
      (QSort sg k es, _) =>
        (\es' => QSort sg k es') <$> contractSpine sig i p es
      _ => Nothing

  contractSpine : Sig -> Nat -> List Nat -> SubNorm -> Maybe SubNorm
  contractSpine sig i p es = do
    let l = toList es
    e <- getAt i l
    e' <- contractAtE sig p e
    l' <- setAt i e' l
    pure (cast l')
   where
    setAt : Nat -> a -> List a -> Maybe (List a)
    setAt _ _ [] = Nothing
    setAt Z x (_ :: rest) = Just (x :: rest)
    setAt (S n) x (y :: rest) = (y ::) <$> setAt n x rest


-- ===== READING AND SEARCHING POSITIONS (companions to contractAt,
-- same child table) =====

mutual
  ||| The subterm at a path — Left for element positions, Right for
  ||| type positions (a path may cross EqTy's ∈-slot or ∥·∥'s body).
  export
  subAtE : List Nat -> Elem -> Maybe (Either Elem Ty)
  subAtE [] e = Just (Left e)
  subAtE (i :: p) e =
    case (e, i) of
      (ZeroElim t, 0) => subAtE p t
      (NatIntro1 t, 0) => subAtE p t
      (NatElim z s t, 0) => subAtE p z
      (NatElim z s t, 1) => subAtE p s
      (NatElim z s t, 2) => subAtE p t
      (PiIntro f, 0) => subAtE p f
      (PiApp f e2, 0) => subAtE p f
      (PiApp f e2, 1) => subAtE p e2
      (Let a b, 0) => subAtE p a
      (Let a b, 1) => subAtE p b
      (SigmaIntro a b, 0) => subAtE p a
      (SigmaIntro a b, 1) => subAtE p b
      (SigmaElim1 t, 0) => subAtE p t
      (SigmaElim2 t, 0) => subAtE p t
      (Inj1 t, 0) => subAtE p t
      (Inj2 t, 0) => subAtE p t
      (SumElim l r t, 0) => subAtE p l
      (SumElim l r t, 1) => subAtE p r
      (SumElim l r t, 2) => subAtE p t
      (Elem.PiTy a b, 0) => subAtE p a
      (Elem.PiTy a b, 1) => subAtE p b
      (Elem.SigmaTy a b, 0) => subAtE p a
      (Elem.SigmaTy a b, 1) => subAtE p b
      (Elem.SumTy a b, 0) => subAtE p a
      (Elem.SumTy a b, 1) => subAtE p b
      (Elem.EqTy l r t, 0) => subAtE p l
      (Elem.EqTy l r t, 1) => subAtE p r
      (Elem.EqTy l r t, 2) => subAtT p t
      (QuotTy a r, 0) => subAtE p a
      (QuotTy a r, 1) => subAtE p r
      (Elem.SigVar x es, _) => do
        e2 <- getAt i (toList es)
        subAtE p e2
      (Class a, 0) => subAtE p a
      (QuotElim f q, 0) => subAtE p f
      (QuotElim f q, 1) => subAtE p q
      (Squash t, 0) => subAtT p t
      (QSortC sg k es, _) => do
        e2 <- getAt i (toList es)
        subAtE p e2
      (QCtor sg k es, _) => do
        e2 <- getAt i (toList es)
        subAtE p e2
      (QElim sg k ms fs es w, _) =>
        if i == length (toList es)
          then subAtE p w
          else do e2 <- getAt i (toList es)
                  subAtE p e2
      (Out t, 0) => subAtE p t
      (Corec pf a f x, 0) => subAtE p a
      (Corec pf a f x, 1) => subAtE p f
      (Corec pf a f x, 2) => subAtE p x
      _ => Nothing

  export
  subAtT : List Nat -> Ty -> Maybe (Either Elem Ty)
  subAtT [] t = Just (Right t)
  subAtT (i :: p) t =
    case (t, i) of
      (Ty.PiTy a b, 0) => subAtT p a
      (Ty.PiTy a b, 1) => subAtT p b
      (Ty.SigmaTy a b, 0) => subAtT p a
      (Ty.SigmaTy a b, 1) => subAtT p b
      (Ty.SumTy a b, 0) => subAtT p a
      (Ty.SumTy a b, 1) => subAtT p b
      (El e, 0) => subAtE p e
      (Prf e, 0) => subAtE p e
      (Quotient a r, 0) => subAtT p a
      (Quotient a r, 1) => subAtE p r
      (Ty.SigVar x es, _) => do
        e2 <- getAt i (toList es)
        subAtE p e2
      (QSort sg k es, _) => do
        e2 <- getAt i (toList es)
        subAtE p e2
      _ => Nothing

mutual
  ||| The outermost-leftmost ≜ redex position inside an element.
  export
  findRedexE : Sig -> Elem -> Maybe (List Nat)
  findRedexE sig e =
    case step1E sig e of
      Just _ => Just []
      Nothing => goKids (childIx e)
   where
    goKids : List (Nat, Either Elem Ty) -> Maybe (List Nat)
    goKids [] = Nothing
    goKids ((i, Left c) :: rest) =
      ((i ::) <$> findRedexE sig c) <|> goKids rest
    goKids ((i, Right c) :: rest) =
      ((i ::) <$> findRedexT sig c) <|> goKids rest

    childIx : Elem -> List (Nat, Either Elem Ty)
    childIx (ZeroElim t) = [(0, Left t)]
    childIx (NatIntro1 t) = [(0, Left t)]
    childIx (NatElim z s t) = [(0, Left z), (1, Left s), (2, Left t)]
    childIx (PiIntro f) = [(0, Left f)]
    childIx (PiApp f e2) = [(0, Left f), (1, Left e2)]
    childIx (Let a b) = [(0, Left a), (1, Left b)]
    childIx (SigmaIntro a b) = [(0, Left a), (1, Left b)]
    childIx (SigmaElim1 t) = [(0, Left t)]
    childIx (SigmaElim2 t) = [(0, Left t)]
    childIx (Inj1 t) = [(0, Left t)]
    childIx (Inj2 t) = [(0, Left t)]
    childIx (SumElim l r t) = [(0, Left l), (1, Left r), (2, Left t)]
    childIx (Elem.PiTy a b) = [(0, Left a), (1, Left b)]
    childIx (Elem.SigmaTy a b) = [(0, Left a), (1, Left b)]
    childIx (Elem.SumTy a b) = [(0, Left a), (1, Left b)]
    childIx (Elem.EqTy l r t) = [(0, Left l), (1, Left r), (2, Right t)]
    childIx (QuotTy a r) = [(0, Left a), (1, Left r)]
    childIx (Elem.SigVar x es) =
      map (\(i, e2) => (i, Left e2))
        (zip [0 .. minus (length (toList es)) 1] (toList es))
    childIx (Class a) = [(0, Left a)]
    childIx (QuotElim f q) = [(0, Left f), (1, Left q)]
    childIx (Squash t) = [(0, Right t)]
    childIx (QSortC sg k es) =
      map (\(i, e2) => (i, Left e2))
        (zip [0 .. minus (length (toList es)) 1] (toList es))
    childIx (QCtor sg k es) =
      map (\(i, e2) => (i, Left e2))
        (zip [0 .. minus (length (toList es)) 1] (toList es))
    childIx (QElim sg k ms fs es w) =
      map (\(i, e2) => (i, Left e2))
        (zip [0 .. minus (length (toList es)) 1] (toList es))
      ++ [(length (toList es), Left w)]
    childIx (Out t) = [(0, Left t)]
    childIx (Corec pf a f x) = [(0, Left a), (1, Left f), (2, Left x)]
    childIx _ = []

  export
  findRedexT : Sig -> Ty -> Maybe (List Nat)
  findRedexT sig t =
    case step1T sig t of
      Just _ => Just []
      Nothing =>
        case t of
          Ty.PiTy a b => ((0 ::) <$> findRedexT sig a) <|> ((1 ::) <$> findRedexT sig b)
          Ty.SigmaTy a b => ((0 ::) <$> findRedexT sig a) <|> ((1 ::) <$> findRedexT sig b)
          Ty.SumTy a b => ((0 ::) <$> findRedexT sig a) <|> ((1 ::) <$> findRedexT sig b)
          El e => (0 ::) <$> findRedexE sig e
          Prf e => (0 ::) <$> findRedexE sig e
          Quotient a r => ((0 ::) <$> findRedexT sig a) <|> ((1 ::) <$> findRedexE sig r)
          _ => Nothing


||| Replace the subterm at a path outright (the positionalizer's
||| untyped lemma application; the caller owns the equality evidence).
export
replaceAtE : List Nat -> Elem -> Elem -> Maybe Elem
replaceAtE [] r _ = Just r
replaceAtE (i :: p) r e =
  case (e, i) of
    (ZeroElim t, 0) => ZeroElim <$> replaceAtE p r t
    (NatIntro1 t, 0) => NatIntro1 <$> replaceAtE p r t
    (NatElim z s t, 0) => (\z' => NatElim z' s t) <$> replaceAtE p r z
    (NatElim z s t, 1) => (\s' => NatElim z s' t) <$> replaceAtE p r s
    (NatElim z s t, 2) => NatElim z s <$> replaceAtE p r t
    (PiIntro f, 0) => PiIntro <$> replaceAtE p r f
    (PiApp f e2, 0) => (\f' => PiApp f' e2) <$> replaceAtE p r f
    (PiApp f e2, 1) => PiApp f <$> replaceAtE p r e2
    (Let a b, 0) => (\a' => Let a' b) <$> replaceAtE p r a
    (Let a b, 1) => Let a <$> replaceAtE p r b
    (SigmaIntro a b, 0) => (\a' => SigmaIntro a' b) <$> replaceAtE p r a
    (SigmaIntro a b, 1) => SigmaIntro a <$> replaceAtE p r b
    (SigmaElim1 t, 0) => SigmaElim1 <$> replaceAtE p r t
    (SigmaElim2 t, 0) => SigmaElim2 <$> replaceAtE p r t
    (Inj1 t, 0) => Inj1 <$> replaceAtE p r t
    (Inj2 t, 0) => Inj2 <$> replaceAtE p r t
    (SumElim l r2 t, 0) => (\l' => SumElim l' r2 t) <$> replaceAtE p r l
    (SumElim l r2 t, 1) => (\r2' => SumElim l r2' t) <$> replaceAtE p r r2
    (SumElim l r2 t, 2) => SumElim l r2 <$> replaceAtE p r t
    (Elem.PiTy a b, 0) => (\a' => Elem.PiTy a' b) <$> replaceAtE p r a
    (Elem.PiTy a b, 1) => Elem.PiTy a <$> replaceAtE p r b
    (Elem.SigmaTy a b, 0) => (\a' => Elem.SigmaTy a' b) <$> replaceAtE p r a
    (Elem.SigmaTy a b, 1) => Elem.SigmaTy a <$> replaceAtE p r b
    (Elem.SumTy a b, 0) => (\a' => Elem.SumTy a' b) <$> replaceAtE p r a
    (Elem.SumTy a b, 1) => Elem.SumTy a <$> replaceAtE p r b
    (Elem.EqTy l r2 t, 0) => (\l' => Elem.EqTy l' r2 t) <$> replaceAtE p r l
    (Elem.EqTy l r2 t, 1) => (\r2' => Elem.EqTy l r2' t) <$> replaceAtE p r r2
    (QuotTy a r2, 0) => (\a' => QuotTy a' r2) <$> replaceAtE p r a
    (QuotTy a r2, 1) => QuotTy a <$> replaceAtE p r r2
    (Elem.SigVar x es, _) => Elem.SigVar x <$> spineSet i p es
    (Class a, 0) => Class <$> replaceAtE p r a
    (QuotElim f q, 0) => (\f' => QuotElim f' q) <$> replaceAtE p r f
    (QuotElim f q, 1) => QuotElim f <$> replaceAtE p r q
    (QSortC sg k es, _) => (\es' => QSortC sg k es') <$> spineSet i p es
    (QCtor sg k es, _) => (\es' => QCtor sg k es') <$> spineSet i p es
    (QElim sg k ms fs es w, _) =>
      if i == length (toList es)
        then QElim sg k ms fs es <$> replaceAtE p r w
        else (\es' => QElim sg k ms fs es' w) <$> spineSet i p es
    (Out t, 0) => Out <$> replaceAtE p r t
    (Corec pf a f x, 0) => (\a' => Corec pf a' f x) <$> replaceAtE p r a
    (Corec pf a f x, 1) => (\f' => Corec pf a f' x) <$> replaceAtE p r f
    (Corec pf a f x, 2) => Corec pf a f <$> replaceAtE p r x
    _ => Nothing
 where
  spineSet : Nat -> List Nat -> SubNorm -> Maybe SubNorm
  spineSet i p es = do
    let l = toList es
    e2 <- getAt i l
    e2' <- replaceAtE p r e2
    l' <- setL i e2' l
    pure (cast l')
   where
    setL : Nat -> a -> List a -> Maybe (List a)
    setL _ _ [] = Nothing
    setL Z x (_ :: rest) = Just (x :: rest)
    setL (S n) x (y :: rest) = (y ::) <$> setL n x rest

||| The PRINCIPAL child of an elimination — the position whose
||| exposure can unlock the head (whnf order).
export
principalIx : Elem -> Maybe Nat
principalIx (PiApp _ _) = Just 0
principalIx (NatElim _ _ _) = Just 2
principalIx (SigmaElim1 _) = Just 0
principalIx (SigmaElim2 _) = Just 0
principalIx (SumElim _ _ _) = Just 2
principalIx (QuotElim _ _) = Just 1
principalIx (QElim _ _ _ _ es _) = Just (length (toList es))
principalIx (Out _) = Just 0
principalIx (Squash _) = Just 0
principalIx _ = Nothing
