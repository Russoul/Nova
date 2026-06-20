module Nova.Foundation.Derivation

import Data.SnocList
import Nova.Foundation.Syntax
import Nova.Foundation.Substitution

||| ↑ⁿ — n-fold weakening in the existing substitution syntax
public export
wkN : Nat -> SubstContext
wkN Z     = Id
wkN (S n) = Chain Wk (wkN n)

||| Variable lookup: HasVar ctx i ty means de Bruijn variable i in ctx has type ty
public export
data HasVar : Ctx -> Nat -> Typ -> Type where
  HereVar  : HasVar (ctx :< ty) 0 ty
  ThereVar : HasVar ctx i ty -> HasVar (ctx :< ty') (S i) ty

mutual

  ||| Γ ctx
  public export
  data CtxWf : Ctx -> Type where
    CtxEmpty : CtxWf [<]
    CtxExt   : TypWf ctx ty -> CtxWf (ctx :< ty)

  ||| Γ = Δ ctx
  public export
  data CtxEq : Ctx -> Ctx -> Type where
    CtxEqRefl   : CtxWf ctx -> CtxEq ctx ctx
    CtxEqSym    : CtxEq ctx1 ctx2 -> CtxEq ctx2 ctx1
    CtxEqTrans  : CtxEq ctx1 ctx2 -> CtxEq ctx2 ctx3 -> CtxEq ctx1 ctx3
    CtxEqExt    : CtxEq ctx1 ctx2 -> TypEq ctx1 ty ty' -> CtxEq (ctx1 :< ty) (ctx2 :< ty')
    CtxEqInjCtx : CtxEq (ctx1 :< ty) (ctx2 :< ty') -> CtxEq ctx1 ctx2

  ||| σ : Γ ⇒ Δ
  public export
  data SubstWf : SubstContext -> Ctx -> Ctx -> Type where
    SubstTerminal : CtxWf ctx -> SubstWf Terminal ctx [<]
    SubstId       : CtxWf ctx -> SubstWf Id ctx ctx
    SubstWk       : CtxWf (ctx :< ty) -> SubstWf Wk (ctx :< ty) ctx
    SubstComp     : SubstWf s ctx1 ctx2 -> SubstWf t ctx0 ctx1 -> SubstWf (Chain s t) ctx0 ctx2
    SubstExt      : SubstWf s ctx0 ctx1 -> TypWf ctx1 ty -> ElWf ctx0 t (SubstElim ty s)
                  -> SubstWf (Ext s t) ctx0 (ctx1 :< ty)
    SubstConvSrc  : SubstWf s ctx ctx1 -> CtxEq ctx ctx' -> SubstWf s ctx' ctx1
    SubstConvTgt  : SubstWf s ctx0 ctx -> CtxEq ctx ctx' -> SubstWf s ctx0 ctx'

  ||| σ = τ : Γ ⇒ Δ
  public export
  data SubstEq : SubstContext -> SubstContext -> Ctx -> Ctx -> Type where
    SubstEqTerminal : CtxWf ctx -> SubstWf s ctx [<] -> SubstEq s Terminal ctx [<]
    SubstEqIdR      : SubstWf s ctx0 ctx1 -> SubstEq (Chain s Id) s ctx0 ctx1
    SubstEqIdL      : SubstWf s ctx0 ctx1 -> SubstEq (Chain Id s) s ctx0 ctx1
    SubstEqAssoc    : SubstWf s01 ctx1 ctx0 -> SubstWf s21 ctx2 ctx1 -> SubstWf s32 ctx3 ctx2
                    -> SubstEq (Chain s01 (Chain s21 s32)) (Chain (Chain s01 s21) s32) ctx3 ctx0
    SubstEqWkExt    : SubstWf s ctx0 ctx1 -> TypWf ctx1 ty -> ElWf ctx0 t (SubstElim ty s)
                    -> SubstEq (Chain Wk (Ext s t)) s ctx0 ctx1
    SubstEqCompExt  : SubstWf tau ctx0 ctx1 -> SubstWf s ctx1 ctx2 -> TypWf ctx2 ty
                    -> ElWf ctx1 t (SubstElim ty s)
                    -> SubstEq (Chain (Ext s t) tau) (Ext (Chain s tau) (SubstElim t tau)) ctx0 (ctx2 :< ty)
    SubstEqRefl     : SubstWf s ctx0 ctx1 -> SubstEq s s ctx0 ctx1
    SubstEqSym      : SubstEq s t ctx0 ctx1 -> SubstEq t s ctx0 ctx1
    SubstEqTrans    : SubstEq s t ctx0 ctx1 -> SubstEq t r ctx0 ctx1 -> SubstEq s r ctx0 ctx1
    SubstEqCongComp : SubstEq s s' ctx1 ctx2 -> SubstEq t t' ctx0 ctx1
                    -> SubstEq (Chain s t) (Chain s' t') ctx0 ctx2
    SubstEqCongExt  : SubstEq s s' ctx0 ctx1 -> TypWf ctx1 ty -> ElEq ctx0 t t' (SubstElim ty s)
                    -> SubstEq (Ext s t) (Ext s' t') ctx0 (ctx1 :< ty)
    SubstEqConvSrc  : SubstEq s t ctx ctx1 -> CtxEq ctx ctx' -> SubstEq s t ctx' ctx1
    SubstEqConvTgt  : SubstEq s t ctx0 ctx -> CtxEq ctx ctx' -> SubstEq s t ctx0 ctx'

  ||| Γ ⊦ A type
  public export
  data TypWf : Ctx -> Typ -> Type where
    TypWfSubst    : TypWf ctx1 ty -> SubstWf s ctx0 ctx1 -> TypWf ctx0 (SubstElim ty s)
    TypWfZero     : CtxWf ctx -> TypWf ctx ZeroTy
    TypWfOne      : CtxWf ctx -> TypWf ctx OneTy
    TypWfNat      : CtxWf ctx -> TypWf ctx NatTy
    TypWfUniverse : CtxWf ctx -> TypWf ctx UniverseTy
    TypWfEl       : ElWf ctx t UniverseTy -> TypWf ctx (El t)
    TypWfPi       : TypWf ctx ty1 -> TypWf (ctx :< ty1) ty2 -> TypWf ctx (PiTy ty1 ty2)
    TypWfSigma    : TypWf ctx ty1 -> TypWf (ctx :< ty1) ty2 -> TypWf ctx (SigmaTy ty1 ty2)
    TypWfEqTy     : TypWf ctx ty -> ElWf ctx t0 ty -> ElWf ctx t1 ty -> TypWf ctx (EqTy t0 t1 ty)
    TypWfConvCtx  : TypWf ctx ty -> CtxEq ctx ctx' -> TypWf ctx' ty

  ||| Γ ⊦ A = B type
  public export
  data TypEq : Ctx -> Typ -> Typ -> Type where
    TypEqRefl          : TypWf ctx ty -> TypEq ctx ty ty
    TypEqSym           : TypEq ctx ty1 ty2 -> TypEq ctx ty2 ty1
    TypEqTrans         : TypEq ctx ty1 ty2 -> TypEq ctx ty2 ty3 -> TypEq ctx ty1 ty3
    TypEqConvCtx       : TypEq ctx ty1 ty2 -> CtxEq ctx ctx' -> TypEq ctx' ty1 ty2
    -- Substitution equalities
    TypEqSubstId       : TypWf ctx ty -> TypEq ctx (SubstElim ty Id) ty
    TypEqSubstComp     : TypWf ctx2 ty -> SubstWf s ctx1 ctx2 -> SubstWf t ctx0 ctx1
                       -> TypEq ctx0 (SubstElim (SubstElim ty s) t) (SubstElim ty (Chain s t))
    TypEqSubstZero     : SubstWf s ctx0 ctx1 -> TypEq ctx0 (SubstElim ZeroTy s) ZeroTy
    TypEqSubstOne      : SubstWf s ctx0 ctx1 -> TypEq ctx0 (SubstElim OneTy s) OneTy
    TypEqSubstNat      : SubstWf s ctx0 ctx1 -> TypEq ctx0 (SubstElim NatTy s) NatTy
    TypEqSubstUniverse : SubstWf s ctx0 ctx1 -> TypEq ctx0 (SubstElim UniverseTy s) UniverseTy
    -- Universe decoding equalities
    TypEqElZero        : CtxWf ctx -> TypEq ctx (El ZeroTy) ZeroTy
    TypEqElOne         : CtxWf ctx -> TypEq ctx (El OneTy) OneTy
    TypEqElNat         : CtxWf ctx -> TypEq ctx (El NatTy) NatTy
    TypEqSubstEl       : ElWf ctx1 t UniverseTy -> SubstWf s ctx0 ctx1
                       -> TypEq ctx0 (SubstElim (El t) s) (El (SubstElim t s))
    TypEqSubstPi       : TypWf ctx1 ty1 -> TypWf (ctx1 :< ty1) ty2 -> SubstWf s ctx0 ctx1
                       -> TypEq ctx0 (SubstElim (PiTy ty1 ty2) s)
                                     (PiTy (SubstElim ty1 s) (SubstElim ty2 (Under s)))
    TypEqElPi          : ElWf ctx a UniverseTy -> ElWf (ctx :< El a) b UniverseTy
                       -> TypEq ctx (El (PiTy a b)) (PiTy (El a) (El b))
    TypEqSubstSigma    : TypWf ctx1 ty1 -> TypWf (ctx1 :< ty1) ty2 -> SubstWf s ctx0 ctx1
                       -> TypEq ctx0 (SubstElim (SigmaTy ty1 ty2) s)
                                     (SigmaTy (SubstElim ty1 s) (SubstElim ty2 (Under s)))
    TypEqElSigma       : ElWf ctx a UniverseTy -> ElWf (ctx :< El a) b UniverseTy
                       -> TypEq ctx (El (SigmaTy a b)) (SigmaTy (El a) (El b))
    TypEqSubstEqTy     : TypWf ctx1 ty -> ElWf ctx1 t0 ty -> ElWf ctx1 t1 ty -> SubstWf s ctx0 ctx1
                       -> TypEq ctx0 (SubstElim (EqTy t0 t1 ty) s)
                                     (EqTy (SubstElim t0 s) (SubstElim t1 s) (SubstElim ty s))
    TypEqElEqTy        : ElWf ctx a UniverseTy -> ElWf ctx t0 (El a) -> ElWf ctx t1 (El a)
                       -> TypEq ctx (El (EqTy t0 t1 a)) (EqTy t0 t1 (El a))
    -- Congruence
    TypEqCongSubst     : TypEq ctx1 ty1 ty2 -> SubstEq s s' ctx0 ctx1
                       -> TypEq ctx0 (SubstElim ty1 s) (SubstElim ty2 s')
    TypEqCongPi        : TypEq ctx ty1 ty1' -> TypEq (ctx :< ty1) ty2 ty2'
                       -> TypEq ctx (PiTy ty1 ty2) (PiTy ty1' ty2')
    TypEqCongSigma     : TypEq ctx ty1 ty1' -> TypEq (ctx :< ty1) ty2 ty2'
                       -> TypEq ctx (SigmaTy ty1 ty2) (SigmaTy ty1' ty2')
    TypEqCongEqTy      : ElEq ctx t0 t0' ty -> ElEq ctx t1 t1' ty -> TypEq ctx ty ty'
                       -> TypEq ctx (EqTy t0 t1 ty) (EqTy t0' t1' ty')
    TypEqCongEl        : ElEq ctx t t' UniverseTy -> TypEq ctx (El t) (El t')
    -- Injectivity of type constructors (return TypEq, so they live here)
    TypEqInjPiL        : TypEq ctx (PiTy ty1 ty2) (PiTy ty1' ty2') -> TypEq ctx ty1 ty1'
    TypEqInjPiR        : TypEq ctx (PiTy ty1 ty2) (PiTy ty1' ty2') -> TypEq (ctx :< ty1) ty2 ty2'
    TypEqInjSigmaL     : TypEq ctx (SigmaTy ty1 ty2) (SigmaTy ty1' ty2') -> TypEq ctx ty1 ty1'
    TypEqInjSigmaR     : TypEq ctx (SigmaTy ty1 ty2) (SigmaTy ty1' ty2') -> TypEq (ctx :< ty1) ty2 ty2'
    TypEqInjEqTyTy     : TypEq ctx (EqTy t0 t1 ty) (EqTy t0' t1' ty') -> TypEq ctx ty ty'
    -- Injectivity of context extension and telescope extension → conclude TypEq
    CtxExtInjTy        : CtxEq (ctx1 :< ty) (ctx2 :< ty') -> TypEq ctx1 ty ty'
    TelExtInjTy        : TelEq ctx (ty1 :: tel1) (ty2 :: tel2) -> TypEq ctx ty1 ty2

  ||| Γ ⊦ Δ tel
  public export
  data TelWf : Ctx -> Tel -> Type where
    TelWfEmpty   : CtxWf ctx -> TelWf ctx []
    TelWfExt     : TypWf ctx ty -> TelWf (ctx :< ty) tel -> TelWf ctx (ty :: tel)
    TelWfSubst   : SubstWf s ctx0 ctx1 -> TelWf ctx1 tel -> TelWf ctx0 (Tel.subst tel s)
    TelWfConvCtx : TelWf ctx tel -> CtxEq ctx ctx' -> TelWf ctx' tel

  ||| Γ ⊦ Δ = Δ' tel
  public export
  data TelEq : Ctx -> Tel -> Tel -> Type where
    TelEqRefl      : TelWf ctx tel -> TelEq ctx tel tel
    TelEqSym       : TelEq ctx tel1 tel2 -> TelEq ctx tel2 tel1
    TelEqTrans     : TelEq ctx tel1 tel2 -> TelEq ctx tel2 tel3 -> TelEq ctx tel1 tel3
    TelEqConvCtx   : TelEq ctx tel1 tel2 -> CtxEq ctx ctx' -> TelEq ctx' tel1 tel2
    -- Congruence
    TelEqCongExt   : TypEq ctx ty1 ty2 -> TelEq (ctx :< ty1) tel1 tel2
                   -> TelEq ctx (ty1 :: tel1) (ty2 :: tel2)
    TelEqCongSubst : TelEq ctx1 tel1 tel2 -> SubstEq s s' ctx0 ctx1
                   -> TelEq ctx0 (Tel.subst tel1 s) (Tel.subst tel2 s')
    -- Injectivity
    TelExtInjTel   : TelEq ctx (ty1 :: tel1) (ty2 :: tel2) -> TelEq (ctx :< ty1) tel1 tel2

  ||| Γ ⊦ a : A
  public export
  data ElWf : Ctx -> Elem -> Typ -> Type where
    -- Universe codes
    ElWfZeroCode  : CtxWf ctx -> ElWf ctx ZeroTy UniverseTy
    ElWfOneCode   : CtxWf ctx -> ElWf ctx OneTy UniverseTy
    ElWfNatCode   : CtxWf ctx -> ElWf ctx NatTy UniverseTy
    ElWfPiCode    : ElWf ctx a UniverseTy -> ElWf (ctx :< El a) b UniverseTy
                  -> ElWf ctx (PiTy a b) UniverseTy
    ElWfSigmaCode : ElWf ctx a UniverseTy -> ElWf (ctx :< El a) b UniverseTy
                  -> ElWf ctx (SigmaTy a b) UniverseTy
    ElWfEqCode    : ElWf ctx a UniverseTy -> ElWf ctx t0 (El a) -> ElWf ctx t1 (El a)
                  -> ElWf ctx (EqTy t0 t1 a) UniverseTy
    -- Canonical elements
    ElWfOneIntro  : CtxWf ctx -> ElWf ctx OneIntro OneTy
    ElWfZeroIntro : CtxWf ctx -> ElWf ctx NatIntro0 NatTy
    ElWfSucc      : ElWf ctx t NatTy -> ElWf ctx (NatIntro1 t) NatTy
    ElWfLam       : ElWf (ctx :< ty1) f ty2 -> ElWf ctx (PiIntro f) (PiTy ty1 ty2)
    ElWfApp       : ElWf ctx f (PiTy ty1 ty2) -> ElWf ctx e ty1
                  -> ElWf ctx (PiElim f e) (SubstElim ty2 (Ext Id e))
    ElWfPair      : ElWf ctx a ty1 -> ElWf ctx b (SubstElim ty2 (Ext Id a))
                  -> ElWf ctx (SigmaIntro a b) (SigmaTy ty1 ty2)
    ElWfFst       : ElWf ctx t (SigmaTy ty1 ty2) -> ElWf ctx (SigmaElim1 t) ty1
    ElWfSnd       : ElWf ctx t (SigmaTy ty1 ty2)
                  -> ElWf ctx (SigmaElim2 t) (SubstElim ty2 (Ext Id (SigmaElim1 t)))
    ElWfRefl      : ElWf ctx t ty -> ElWf ctx Refl (EqTy t t ty)
    ElWfZeroElim  : TypWf ctx ty -> ElWf ctx t ZeroTy -> ElWf ctx (ZeroElim t) ty
    ElWfNatElim   : TypWf (ctx :< NatTy) motive
                  -> ElWf ctx z (SubstElim motive (Ext Id NatIntro0))
                  -> ElWf (ctx :< NatTy :< motive) s (SubstElim motive (Ext Wk (NatIntro1 (CtxVar 0))))
                  -> ElWf ctx t NatTy
                  -> ElWf ctx (NatElim motive z s t) (SubstElim motive (Ext Id t))
    -- Variable: HasVar captures |Γ₁| = i and A at position i
    ElWfVar       : HasVar ctx i ty -> ElWf ctx (CtxVar i) (SubstElim ty (wkN (S i)))
    -- Substitution
    ElWfSubst     : ElWf ctx1 t ty -> SubstWf s ctx0 ctx1
                  -> ElWf ctx0 (SubstElim t s) (SubstElim ty s)
    -- Conversion
    ElWfConvTy    : ElWf ctx t ty -> TypEq ctx ty ty' -> ElWf ctx t ty'
    ElWfConvCtx   : ElWf ctx t ty -> CtxEq ctx ctx' -> ElWf ctx' t ty

  ||| Γ ⊦ a = b : A
  public export
  data ElEq : Ctx -> Elem -> Elem -> Typ -> Type where
    -- Structural
    ElEqRefl    : ElWf ctx t ty -> ElEq ctx t t ty
    ElEqSym     : ElEq ctx t t' ty -> ElEq ctx t' t ty
    ElEqTrans   : ElEq ctx t t' ty -> ElEq ctx t' t'' ty -> ElEq ctx t t'' ty
    ElEqConvTy  : ElEq ctx t t' ty -> TypEq ctx ty ty' -> ElEq ctx t t' ty'
    ElEqConvCtx : ElEq ctx t t' ty -> CtxEq ctx ctx' -> ElEq ctx' t t' ty
    -- Substitution equalities for elements
    ElEqSubstId        : ElWf ctx t ty -> ElEq ctx (SubstElim t Id) t ty
    ElEqSubstComp      : ElWf ctx2 t ty -> SubstWf s ctx1 ctx2 -> SubstWf tau ctx0 ctx1
                       -> ElEq ctx0 (SubstElim (SubstElim t s) tau) (SubstElim t (Chain s tau))
                                (SubstElim ty (Chain s tau))
    ElEqSubstOneIntro  : SubstWf s ctx0 ctx1 -> ElEq ctx0 (SubstElim OneIntro s) OneIntro OneTy
    ElEqSubstZeroIntro : SubstWf s ctx0 ctx1 -> ElEq ctx0 (SubstElim NatIntro0 s) NatIntro0 NatTy
    ElEqSubstSucc      : ElWf ctx1 t NatTy -> SubstWf s ctx0 ctx1
                       -> ElEq ctx0 (SubstElim (NatIntro1 t) s) (NatIntro1 (SubstElim t s)) NatTy
    ElEqSubstZeroCode  : SubstWf s ctx0 ctx1 -> ElEq ctx0 (SubstElim ZeroTy s) ZeroTy UniverseTy
    ElEqSubstOneCode   : SubstWf s ctx0 ctx1 -> ElEq ctx0 (SubstElim OneTy s) OneTy UniverseTy
    ElEqSubstNatCode   : SubstWf s ctx0 ctx1 -> ElEq ctx0 (SubstElim NatTy s) NatTy UniverseTy
    ElEqSubstPiCode    : ElWf ctx1 a UniverseTy -> ElWf (ctx1 :< El a) b UniverseTy
                       -> SubstWf s ctx0 ctx1
                       -> ElEq ctx0 (SubstElim (PiTy a b) s)
                                    (PiTy (SubstElim a s) (SubstElim b (Under s)))
                                    UniverseTy
    ElEqSubstSigmaCode : ElWf ctx1 a UniverseTy -> ElWf (ctx1 :< El a) b UniverseTy
                       -> SubstWf s ctx0 ctx1
                       -> ElEq ctx0 (SubstElim (SigmaTy a b) s)
                                    (SigmaTy (SubstElim a s) (SubstElim b (Under s)))
                                    UniverseTy
    ElEqSubstEqCode    : ElWf ctx1 a UniverseTy -> ElWf ctx1 t0 (El a) -> ElWf ctx1 t1 (El a)
                       -> SubstWf s ctx0 ctx1
                       -> ElEq ctx0 (SubstElim (EqTy t0 t1 a) s)
                                    (EqTy (SubstElim t0 s) (SubstElim t1 s) (SubstElim a s))
                                    UniverseTy
    ElEqSubstLam       : ElWf (ctx1 :< ty1) f ty2 -> SubstWf s ctx0 ctx1
                       -> ElEq ctx0 (SubstElim (PiIntro f) s)
                                    (PiIntro (SubstElim f (Under s)))
                                    (PiTy (SubstElim ty1 s) (SubstElim ty2 (Under s)))
    ElEqSubstApp       : ElWf ctx1 f (PiTy ty1 ty2) -> ElWf ctx1 e ty1 -> SubstWf s ctx0 ctx1
                       -> ElEq ctx0 (SubstElim (PiElim f e) s)
                                    (PiElim (SubstElim f s) (SubstElim e s))
                                    (SubstElim ty2 (Ext s (SubstElim e s)))
    ElEqSubstPair      : ElWf ctx1 a ty1 -> ElWf ctx1 b (SubstElim ty2 (Ext Id a))
                       -> SubstWf s ctx0 ctx1
                       -> ElEq ctx0 (SubstElim (SigmaIntro a b) s)
                                    (SigmaIntro (SubstElim a s) (SubstElim b s))
                                    (SigmaTy (SubstElim ty1 s) (SubstElim ty2 (Under s)))
    ElEqSubstFst       : ElWf ctx1 t (SigmaTy ty1 ty2) -> SubstWf s ctx0 ctx1
                       -> ElEq ctx0 (SubstElim (SigmaElim1 t) s)
                                    (SigmaElim1 (SubstElim t s))
                                    (SubstElim ty1 s)
    ElEqSubstSnd       : ElWf ctx1 t (SigmaTy ty1 ty2) -> SubstWf s ctx0 ctx1
                       -> ElEq ctx0 (SubstElim (SigmaElim2 t) s)
                                    (SigmaElim2 (SubstElim t s))
                                    (SubstElim ty2 (Ext s (SigmaElim1 (SubstElim t s))))
    ElEqSubstRefl      : ElWf ctx1 a ty -> SubstWf s ctx0 ctx1
                       -> ElEq ctx0 (SubstElim Refl s)
                                    Refl
                                    (EqTy (SubstElim a s) (SubstElim a s) (SubstElim ty s))
    ElEqSubstZeroElim  : TypWf ctx1 ty -> ElWf ctx1 t ZeroTy -> SubstWf s ctx0 ctx1
                       -> ElEq ctx0 (SubstElim (ZeroElim t) s)
                                    (ZeroElim (SubstElim t s))
                                    (SubstElim ty s)
    ElEqSubstNatElim   : TypWf (ctx1 :< NatTy) motive
                       -> ElWf ctx1 z (SubstElim motive (Ext Id NatIntro0))
                       -> ElWf (ctx1 :< NatTy :< motive) step
                                (SubstElim motive (Ext Wk (NatIntro1 (CtxVar 0))))
                       -> ElWf ctx1 t NatTy -> SubstWf s ctx0 ctx1
                       -> ElEq ctx0 (SubstElim (NatElim motive z step t) s)
                                    (NatElim (SubstElim motive (Under s))
                                             (SubstElim z s)
                                             (SubstElim step (Under (Under s)))
                                             (SubstElim t s))
                                    (SubstElim motive (Ext s (SubstElim t s)))
    -- β/η rules
    ElEqOneEta     : ElWf ctx t OneTy -> ElEq ctx t OneIntro OneTy
    ElEqPiBeta     : ElWf (ctx :< ty1) f ty2 -> ElWf ctx e ty1
                   -> ElEq ctx (PiElim (PiIntro f) e) (SubstElim f (Ext Id e))
                            (SubstElim ty2 (Ext Id e))
    ElEqPiEta      : ElWf ctx f (PiTy ty1 ty2)
                   -> ElEq ctx (PiIntro (PiElim (SubstElim f Wk) (CtxVar 0))) f (PiTy ty1 ty2)
    ElEqSigmaBeta1 : TypWf (ctx :< ty1) ty2 -> ElWf ctx a ty1 -> ElWf ctx b (SubstElim ty2 (Ext Id a))
                   -> ElEq ctx (SigmaElim1 (SigmaIntro a b)) a ty1
    ElEqSigmaBeta2 : TypWf (ctx :< ty1) ty2 -> ElWf ctx a ty1 -> ElWf ctx b (SubstElim ty2 (Ext Id a))
                   -> ElEq ctx (SigmaElim2 (SigmaIntro a b)) b (SubstElim ty2 (Ext Id a))
    ElEqSigmaEta   : ElWf ctx t (SigmaTy ty1 ty2)
                   -> ElEq ctx (SigmaIntro (SigmaElim1 t) (SigmaElim2 t)) t (SigmaTy ty1 ty2)
    -- Variable computation rules
    ElEqVar0   : TypWf ctx1 ty -> SubstWf s ctx0 ctx1 -> ElWf ctx0 t (SubstElim ty s)
               -> ElEq ctx0 (SubstElim (CtxVar 0) (Ext s t)) t (SubstElim ty s)
    ElEqVarWk  : HasVar ctx i ty -> TypWf ctx bty
               -> ElEq (ctx :< bty)
                        (SubstElim (CtxVar i) Wk)
                        (CtxVar (S i))
                        (SubstElim ty (wkN (S (S i))))
    -- ℕ-elim β rules
    ElEqNatBeta0 : TypWf (ctx :< NatTy) motive
                 -> ElWf ctx z (SubstElim motive (Ext Id NatIntro0))
                 -> ElWf (ctx :< NatTy :< motive) step
                          (SubstElim motive (Ext Wk (NatIntro1 (CtxVar 0))))
                 -> ElEq ctx (NatElim motive z step NatIntro0) z
                          (SubstElim motive (Ext Id NatIntro0))
    ElEqNatBeta1 : TypWf (ctx :< NatTy) motive
                 -> ElWf ctx z (SubstElim motive (Ext Id NatIntro0))
                 -> ElWf (ctx :< NatTy :< motive) step
                          (SubstElim motive (Ext Wk (NatIntro1 (CtxVar 0))))
                 -> ElWf ctx t NatTy
                 -> ElEq ctx (NatElim motive z step (NatIntro1 t))
                          (SubstElim step (Ext (Ext Id t) (NatElim motive z step t)))
                          (SubstElim motive (Ext Id (NatIntro1 t)))
    -- Equality reflection
    ElEqReflection : ElWf ctx a (EqTy t0 t1 ty) -> ElEq ctx t0 t1 ty
    -- Congruence for element constructors
    ElEqCongSubst      : ElEq ctx1 t t' ty -> SubstEq s s' ctx0 ctx1
                       -> ElEq ctx0 (SubstElim t s) (SubstElim t' s') (SubstElim ty s)
    ElEqCongLam        : ElEq (ctx :< ty1) f f' ty2
                       -> ElEq ctx (PiIntro f) (PiIntro f') (PiTy ty1 ty2)
    ElEqCongApp        : ElEq ctx f f' (PiTy ty1 ty2) -> ElEq ctx e e' ty1
                       -> ElEq ctx (PiElim f e) (PiElim f' e') (SubstElim ty2 (Ext Id e))
    ElEqCongPair       : ElEq ctx a a' ty1 -> ElEq ctx b b' (SubstElim ty2 (Ext Id a))
                       -> ElEq ctx (SigmaIntro a b) (SigmaIntro a' b') (SigmaTy ty1 ty2)
    ElEqCongFst        : ElEq ctx t t' (SigmaTy ty1 ty2)
                       -> ElEq ctx (SigmaElim1 t) (SigmaElim1 t') ty1
    ElEqCongSnd        : ElEq ctx t t' (SigmaTy ty1 ty2)
                       -> ElEq ctx (SigmaElim2 t) (SigmaElim2 t')
                                (SubstElim ty2 (Ext Id (SigmaElim1 t)))
    ElEqCongSucc       : ElEq ctx t t' NatTy -> ElEq ctx (NatIntro1 t) (NatIntro1 t') NatTy
    ElEqCongNatElim    : TypEq (ctx :< NatTy) motive motive'
                       -> ElEq ctx z z' (SubstElim motive (Ext Id NatIntro0))
                       -> ElEq (ctx :< NatTy :< motive) step step'
                                (SubstElim motive (Ext Wk (NatIntro1 (CtxVar 0))))
                       -> ElEq ctx t t' NatTy
                       -> ElEq ctx (NatElim motive z step t) (NatElim motive' z' step' t')
                                (SubstElim motive (Ext Id t))
    ElEqCongZeroElim   : TypWf ctx ty -> ElEq ctx t t' ZeroTy
                       -> ElEq ctx (ZeroElim t) (ZeroElim t') ty
    ElEqCongPiCode     : ElEq ctx a a' UniverseTy -> ElEq (ctx :< El a) b b' UniverseTy
                       -> ElEq ctx (PiTy a b) (PiTy a' b') UniverseTy
    ElEqCongSigmaCode  : ElEq ctx a a' UniverseTy -> ElEq (ctx :< El a) b b' UniverseTy
                       -> ElEq ctx (SigmaTy a b) (SigmaTy a' b') UniverseTy
    ElEqCongEqCode     : ElEq ctx t0 t0' (El a) -> ElEq ctx t1 t1' (El a) -> ElEq ctx a a' UniverseTy
                       -> ElEq ctx (EqTy t0 t1 a) (EqTy t0' t1' a') UniverseTy
    -- Injectivity of successor and universe codes
    ElEqInjSucc        : ElEq ctx (NatIntro1 t) (NatIntro1 t') NatTy -> ElEq ctx t t' NatTy
    ElEqInjPiCodeL     : ElEq ctx (PiTy a b) (PiTy a' b') UniverseTy -> ElEq ctx a a' UniverseTy
    ElEqInjPiCodeR     : ElEq ctx (PiTy a b) (PiTy a' b') UniverseTy
                       -> ElEq (ctx :< El a) b b' UniverseTy
    ElEqInjSigmaCodeL  : ElEq ctx (SigmaTy a b) (SigmaTy a' b') UniverseTy -> ElEq ctx a a' UniverseTy
    ElEqInjSigmaCodeR  : ElEq ctx (SigmaTy a b) (SigmaTy a' b') UniverseTy
                       -> ElEq (ctx :< El a) b b' UniverseTy
    ElEqInjEqCodeTy    : ElEq ctx (EqTy t0 t1 a) (EqTy t0' t1' a') UniverseTy
                       -> ElEq ctx a a' UniverseTy
    ElEqInjEqCodeL     : ElEq ctx (EqTy t0 t1 a) (EqTy t0' t1' a') UniverseTy
                       -> ElEq ctx t0 t0' (El a)
    ElEqInjEqCodeR     : ElEq ctx (EqTy t0 t1 a) (EqTy t0' t1' a') UniverseTy
                       -> ElEq ctx t1 t1' (El a)
    -- Injectivity of EqTy and El type constructors → conclude ElEq
    EqTyInjL   : TypEq ctx (EqTy t0 t1 ty) (EqTy t0' t1' ty') -> ElEq ctx t0 t0' ty
    EqTyInjR   : TypEq ctx (EqTy t0 t1 ty) (EqTy t0' t1' ty') -> ElEq ctx t1 t1' ty
    ElTypInjEl : TypEq ctx (El t) (El t') -> ElEq ctx t t' UniverseTy
    -- Injectivity of element list head → conclude ElEq
    ElListInjHead : ElListEq ctx (e :: es) (e' :: es') (ty :: tel) -> ElEq ctx e e' ty

  ||| Γ ⊦ ē : Δ
  public export
  data ElListWf : Ctx -> ElemList -> Tel -> Type where
    ElListWfNil     : CtxWf ctx -> ElListWf ctx [] []
    ElListWfCons    : TelWf ctx tel -> ElWf ctx e ty
                    -> ElListWf ctx es (Tel.subst tel (Ext Id e))
                    -> ElListWf ctx (e :: es) (ty :: tel)
    ElListWfSubst   : TelWf ctx1 tel -> ElListWf ctx1 es tel -> SubstWf s ctx0 ctx1
                    -> ElListWf ctx0 (ElemList.subst es s) (Tel.subst tel s)
    ElListWfConvCtx : ElListWf ctx es tel -> CtxEq ctx ctx' -> ElListWf ctx' es tel
    ElListWfConvTel : ElListWf ctx es tel -> TelEq ctx tel tel' -> ElListWf ctx es tel'

  ||| Γ ⊦ ē = ē' : Δ
  public export
  data ElListEq : Ctx -> ElemList -> ElemList -> Tel -> Type where
    ElListEqRefl      : ElListWf ctx es tel -> ElListEq ctx es es tel
    ElListEqSym       : ElListEq ctx es es' tel -> ElListEq ctx es' es tel
    ElListEqTrans     : ElListEq ctx es es' tel -> ElListEq ctx es' es'' tel
                      -> ElListEq ctx es es'' tel
    ElListEqConvCtx   : ElListEq ctx es es' tel -> CtxEq ctx ctx'
                      -> ElListEq ctx' es es' tel
    ElListEqConvTel   : ElListEq ctx es es' tel -> TelEq ctx tel tel'
                      -> ElListEq ctx es es' tel'
    ElListEqNil       : CtxWf ctx -> ElListEq ctx [] [] []
    ElListEqCons      : ElEq ctx e0 e1 ty
                      -> ElListEq ctx es0 es1 (Tel.subst tel (Ext Id e0))
                      -> ElListEq ctx (e0 :: es0) (e1 :: es1) (ty :: tel)
    ElListEqCongSubst : ElListEq ctx1 es es' tel -> SubstEq s s' ctx0 ctx1
                      -> ElListEq ctx0 (ElemList.subst es s)
                                       (ElemList.subst es' s')
                                       (Tel.subst tel s)
    ElListInjTail     : ElListEq ctx (e :: es) (e' :: es') (ty :: tel)
                      -> ElListEq ctx es es' (Tel.subst tel (Ext Id e))
