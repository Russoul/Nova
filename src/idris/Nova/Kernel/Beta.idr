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
-- El-(/) (El (A / R) ≜ El A / El R) from docs/NovaFoundation.txt is handled
-- the same way as El-(→)/El-(⨯): Elem.QuotTy is the universe code, decoded
-- by betaTy's El case below.

import Nova.Kernel.Syntax
import Nova.Kernel.Subst

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
  betaElem sig (Elem.EqTy l r t)  = Elem.EqTy (betaElem sig l) (betaElem sig r) (betaElem sig t)
  betaElem sig (QuotTy a r)       = QuotTy (betaElem sig a) (betaElem sig r)
  betaElem sig Refl               = Refl
  betaElem sig (SigVar x es) =
    let es' = betaSubNorm sig es
    in case sigLookup x sig of
         Just (SigDef _ _ a _) => betaElem sig (substElem a (embed es'))
         Just (SigTyDef _ _ _) => assert_total $ idris_crash "betaElem: signature identifier '\{x}' is a type definition, used as a term"
         Nothing               => assert_total $ idris_crash "betaElem: signature identifier '\{x}' not found"
  betaElem sig (Class a)          = Class (betaElem sig a)
  betaElem sig (QuotElim f q) =
    case betaElem sig q of
      Class a => betaElem sig (substElem (betaElem sig f) (Ext Id a))
      q'      => QuotElim (betaElem sig f) q'

||| T, with every beta-redex rewritten: Π/Σ/ℕ-elim/quot-elim/x-β redexes
||| inside an El t's argument (via betaElem), type-level x-β (unfolding a
||| signature type definition x[e˲] ≜ A[e˲]), plus El-of-universe-code
||| decoding — El 𝟘 ≜ 𝟘, El 𝟙 ≜ 𝟙, El ℕ ≜ ℕ, El (A → B) ≜ El A → El B,
||| El (A ⨯ B) ≜ El A ⨯ El B, El (a ≡ b ∈ A) ≜ (a ≡ b ∈ El A),
||| El (A / R) ≜ El A / El R — see the
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
betaTy sig (EqTy l r ty)    = EqTy (betaElem sig l) (betaElem sig r) (betaTy sig ty)
betaTy sig (El e) =
  case betaElem sig e of
    Elem.ZeroTy      => Ty.ZeroTy
    Elem.OneTy       => Ty.OneTy
    Elem.NatTy       => Ty.NatTy
    Elem.PiTy a b    => betaTy sig (Ty.PiTy (El a) (El b))
    Elem.SigmaTy a b => betaTy sig (Ty.SigmaTy (El a) (El b))
    Elem.EqTy l r t  => betaTy sig (EqTy l r (El t))
    QuotTy a r       => betaTy sig (Quotient (El a) (El r))
    e'               => El e'
betaTy sig (Quotient a r)   = Quotient (betaTy sig a) (betaTy sig r)
betaTy sig (Ty.SigVar x es) =
  let es' = betaSubNorm sig es
  in case sigLookup x sig of
       Just (SigTyDef _ _ a) => betaTy sig (substTy a (embed es'))
       Just (SigDef _ _ _ _) => assert_total $ idris_crash "betaTy: signature identifier '\{x}' is a term definition, used as a type"
       Nothing               => assert_total $ idris_crash "betaTy: signature identifier '\{x}' not found"

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
