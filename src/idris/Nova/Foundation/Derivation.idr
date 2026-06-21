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
    CtxExt   : TypWf ctx wf ty -> CtxWf (ctx :< ty)

  ||| Γ = Δ ctx  (indexed by both wf proofs)
  public export
  data CtxEq : (ctx1 : Ctx) -> CtxWf ctx1 -> (ctx2 : Ctx) -> CtxWf ctx2 -> Type where
    CtxEqRefl   : CtxEq ctx wf ctx wf
    CtxEqSym    : CtxEq ctx1 wf1 ctx2 wf2 -> CtxEq ctx2 wf2 ctx1 wf1
    CtxEqTrans  : CtxEq ctx1 wf1 ctx2 wf2 -> CtxEq ctx2 wf2 ctx3 wf3
                -> CtxEq ctx1 wf1 ctx3 wf3
    CtxEqExt    : CtxEq ctx1 wf1 ctx2 wf2
                -> (tywf1 : TypWf ctx1 wf1 ty)
                -> (tywf2 : TypWf ctx2 wf2 ty')
                -> TypEq ctx1 wf1 ty ty'
                -> CtxEq (ctx1 :< ty) (CtxExt tywf1) (ctx2 :< ty') (CtxExt tywf2)
    CtxEqInjCtx : CtxEq (ctx1 :< ty) (CtxExt tywf1) (ctx2 :< ty') (CtxExt tywf2)
                -> CtxEq ctx1 wf1 ctx2 wf2

  ||| σ : Γ ⇒ Δ  (indexed by src and tgt wf proofs)
  public export
  data SubstWf : SubstContext -> (ctx0 : Ctx) -> CtxWf ctx0 -> (ctx1 : Ctx) -> CtxWf ctx1 -> Type where
    SubstTerminal : SubstWf Terminal ctx wf [<] CtxEmpty
    SubstId       : SubstWf Id ctx wf ctx wf
    SubstWk       : SubstWf Wk (ctx :< ty) (CtxExt tywf) ctx wf
    SubstComp     : SubstWf s ctx1 wf1 ctx2 wf2 -> SubstWf t ctx0 wf0 ctx1 wf1
                  -> SubstWf (Chain s t) ctx0 wf0 ctx2 wf2
    SubstExt      : SubstWf s ctx0 wf0 ctx1 wf1 -> (tywf : TypWf ctx1 wf1 ty)
                  -> ElWf ctx0 wf0 t (SubstElim ty s)
                  -> SubstWf (Ext s t) ctx0 wf0 (ctx1 :< ty) (CtxExt tywf)
    SubstConvSrc  : SubstWf s ctx wf ctx1 wf1 -> CtxEq ctx wf ctx' wf'
                  -> SubstWf s ctx' wf' ctx1 wf1
    SubstConvTgt  : SubstWf s ctx0 wf0 ctx wf -> CtxEq ctx wf ctx' wf'
                  -> SubstWf s ctx0 wf0 ctx' wf'

  ||| σ = τ : Γ ⇒ Δ  (indexed by src and tgt wf proofs)
  public export
  data SubstEq : SubstContext -> SubstContext -> (ctx0 : Ctx) -> CtxWf ctx0 -> (ctx1 : Ctx) -> CtxWf ctx1 -> Type where
    SubstEqTerminal : SubstWf s ctx wf [<] CtxEmpty
                    -> SubstEq s Terminal ctx wf [<] CtxEmpty
    SubstEqIdR      : SubstWf s ctx0 wf0 ctx1 wf1
                    -> SubstEq (Chain s Id) s ctx0 wf0 ctx1 wf1
    SubstEqIdL      : SubstWf s ctx0 wf0 ctx1 wf1
                    -> SubstEq (Chain Id s) s ctx0 wf0 ctx1 wf1
    SubstEqAssoc    : SubstWf s01 ctx1 wf1 ctx0 wf0
                    -> SubstWf s21 ctx2 wf2 ctx1 wf1
                    -> SubstWf s32 ctx3 wf3 ctx2 wf2
                    -> SubstEq (Chain s01 (Chain s21 s32)) (Chain (Chain s01 s21) s32) ctx3 wf3 ctx0 wf0
    SubstEqWkExt    : SubstWf s ctx0 wf0 ctx1 wf1
                    -> (tywf : TypWf ctx1 wf1 ty)
                    -> ElWf ctx0 wf0 t (SubstElim ty s)
                    -> SubstEq (Chain Wk (Ext s t)) s ctx0 wf0 ctx1 wf1
    SubstEqCompExt  : SubstWf tau ctx0 wf0 ctx1 wf1
                    -> SubstWf s ctx1 wf1 ctx2 wf2
                    -> (tywf : TypWf ctx2 wf2 ty)
                    -> ElWf ctx1 wf1 t (SubstElim ty s)
                    -> SubstEq (Chain (Ext s t) tau) (Ext (Chain s tau) (SubstElim t tau))
                               ctx0 wf0 (ctx2 :< ty) (CtxExt tywf)
    SubstEqRefl     : SubstWf s ctx0 wf0 ctx1 wf1
                    -> SubstEq s s ctx0 wf0 ctx1 wf1
    SubstEqSym      : SubstEq s t ctx0 wf0 ctx1 wf1 -> SubstEq t s ctx0 wf0 ctx1 wf1
    SubstEqTrans    : SubstEq s t ctx0 wf0 ctx1 wf1 -> SubstEq t r ctx0 wf0 ctx1 wf1
                    -> SubstEq s r ctx0 wf0 ctx1 wf1
    SubstEqCongComp : SubstEq s s' ctx1 wf1 ctx2 wf2 -> SubstEq t t' ctx0 wf0 ctx1 wf1
                    -> SubstEq (Chain s t) (Chain s' t') ctx0 wf0 ctx2 wf2
    SubstEqCongExt  : SubstEq s s' ctx0 wf0 ctx1 wf1
                    -> (tywf : TypWf ctx1 wf1 ty)
                    -> ElEq ctx0 wf0 t t' (SubstElim ty s)
                    -> SubstEq (Ext s t) (Ext s' t') ctx0 wf0 (ctx1 :< ty) (CtxExt tywf)
    SubstEqConvSrc  : SubstEq s t ctx wf ctx1 wf1 -> CtxEq ctx wf ctx' wf'
                    -> SubstEq s t ctx' wf' ctx1 wf1
    SubstEqConvTgt  : SubstEq s t ctx0 wf0 ctx wf -> CtxEq ctx wf ctx' wf'
                    -> SubstEq s t ctx0 wf0 ctx' wf'

  ||| Γ ⊦ A type  (indexed by CtxWf ctx)
  public export
  data TypWf : (ctx : Ctx) -> CtxWf ctx -> Typ -> Type where
    TypWfSubst    : TypWf ctx1 wf1 ty -> SubstWf s ctx0 wf0 ctx1 wf1
                  -> TypWf ctx0 wf0 (SubstElim ty s)
    TypWfZero     : TypWf ctx wf ZeroTy
    TypWfOne      : TypWf ctx wf OneTy
    TypWfNat      : TypWf ctx wf NatTy
    TypWfUniverse : TypWf ctx wf UniverseTy
    TypWfEl       : ElWf ctx wf t UniverseTy -> TypWf ctx wf (El t)
    TypWfPi       : (ty1wf : TypWf ctx wf ty1) -> TypWf (ctx :< ty1) (CtxExt ty1wf) ty2
                  -> TypWf ctx wf (PiTy ty1 ty2)
    TypWfSigma    : (ty1wf : TypWf ctx wf ty1) -> TypWf (ctx :< ty1) (CtxExt ty1wf) ty2
                  -> TypWf ctx wf (SigmaTy ty1 ty2)
    TypWfEqTy     : TypWf ctx wf ty -> ElWf ctx wf t0 ty -> ElWf ctx wf t1 ty
                  -> TypWf ctx wf (EqTy t0 t1 ty)
    TypWfConvCtx  : TypWf ctx wf ty -> CtxEq ctx wf ctx' wf' -> TypWf ctx' wf' ty

  ||| Γ ⊦ A = B type  (indexed by CtxWf ctx)
  public export
  data TypEq : (ctx : Ctx) -> CtxWf ctx -> Typ -> Typ -> Type where
    TypEqRefl          : TypWf ctx wf ty -> TypEq ctx wf ty ty
    TypEqSym           : TypEq ctx wf ty1 ty2 -> TypEq ctx wf ty2 ty1
    TypEqTrans         : TypEq ctx wf ty1 ty2 -> TypEq ctx wf ty2 ty3 -> TypEq ctx wf ty1 ty3
    TypEqConvCtx       : TypEq ctx wf ty1 ty2 -> CtxEq ctx wf ctx' wf' -> TypEq ctx' wf' ty1 ty2
    -- Substitution equalities
    TypEqSubstId       : TypWf ctx wf ty -> TypEq ctx wf (SubstElim ty Id) ty
    TypEqSubstComp     : TypWf ctx2 wf2 ty -> SubstWf s ctx1 wf1 ctx2 wf2 -> SubstWf t ctx0 wf0 ctx1 wf1
                       -> TypEq ctx0 wf0 (SubstElim (SubstElim ty s) t) (SubstElim ty (Chain s t))
    TypEqSubstZero     : SubstWf s ctx0 wf0 ctx1 wf1 -> TypEq ctx0 wf0 (SubstElim ZeroTy s) ZeroTy
    TypEqSubstOne      : SubstWf s ctx0 wf0 ctx1 wf1 -> TypEq ctx0 wf0 (SubstElim OneTy s) OneTy
    TypEqSubstNat      : SubstWf s ctx0 wf0 ctx1 wf1 -> TypEq ctx0 wf0 (SubstElim NatTy s) NatTy
    TypEqSubstUniverse : SubstWf s ctx0 wf0 ctx1 wf1 -> TypEq ctx0 wf0 (SubstElim UniverseTy s) UniverseTy
    -- Universe decoding equalities
    TypEqElZero        : TypEq ctx wf (El ZeroTy) ZeroTy
    TypEqElOne         : TypEq ctx wf (El OneTy) OneTy
    TypEqElNat         : TypEq ctx wf (El NatTy) NatTy
    TypEqSubstEl       : ElWf ctx1 wf1 t UniverseTy -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> TypEq ctx0 wf0 (SubstElim (El t) s) (El (SubstElim t s))
    TypEqSubstPi       : (ty1wf : TypWf ctx1 wf1 ty1) -> TypWf (ctx1 :< ty1) (CtxExt ty1wf) ty2
                       -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> TypEq ctx0 wf0 (SubstElim (PiTy ty1 ty2) s)
                                         (PiTy (SubstElim ty1 s) (SubstElim ty2 (Under s)))
    TypEqElPi          : (awf : ElWf ctx wf a UniverseTy)
                       -> ElWf (ctx :< El a) (CtxExt (TypWfEl awf)) b UniverseTy
                       -> TypEq ctx wf (El (PiTy a b)) (PiTy (El a) (El b))
    TypEqSubstSigma    : (ty1wf : TypWf ctx1 wf1 ty1) -> TypWf (ctx1 :< ty1) (CtxExt ty1wf) ty2
                       -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> TypEq ctx0 wf0 (SubstElim (SigmaTy ty1 ty2) s)
                                         (SigmaTy (SubstElim ty1 s) (SubstElim ty2 (Under s)))
    TypEqElSigma       : (awf : ElWf ctx wf a UniverseTy)
                       -> ElWf (ctx :< El a) (CtxExt (TypWfEl awf)) b UniverseTy
                       -> TypEq ctx wf (El (SigmaTy a b)) (SigmaTy (El a) (El b))
    TypEqSubstEqTy     : TypWf ctx1 wf1 ty -> ElWf ctx1 wf1 t0 ty -> ElWf ctx1 wf1 t1 ty
                       -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> TypEq ctx0 wf0 (SubstElim (EqTy t0 t1 ty) s)
                                         (EqTy (SubstElim t0 s) (SubstElim t1 s) (SubstElim ty s))
    TypEqElEqTy        : ElWf ctx wf a UniverseTy -> ElWf ctx wf t0 (El a) -> ElWf ctx wf t1 (El a)
                       -> TypEq ctx wf (El (EqTy t0 t1 a)) (EqTy t0 t1 (El a))
    -- Congruence
    TypEqCongSubst     : TypEq ctx1 wf1 ty1 ty2 -> SubstEq s s' ctx0 wf0 ctx1 wf1
                       -> TypEq ctx0 wf0 (SubstElim ty1 s) (SubstElim ty2 s')
    TypEqCongPi        : (ty1wf : TypWf ctx wf ty1) -> TypEq ctx wf ty1 ty1'
                       -> TypEq (ctx :< ty1) (CtxExt ty1wf) ty2 ty2'
                       -> TypEq ctx wf (PiTy ty1 ty2) (PiTy ty1' ty2')
    TypEqCongSigma     : (ty1wf : TypWf ctx wf ty1) -> TypEq ctx wf ty1 ty1'
                       -> TypEq (ctx :< ty1) (CtxExt ty1wf) ty2 ty2'
                       -> TypEq ctx wf (SigmaTy ty1 ty2) (SigmaTy ty1' ty2')
    TypEqCongEqTy      : ElEq ctx wf t0 t0' ty -> ElEq ctx wf t1 t1' ty -> TypEq ctx wf ty ty'
                       -> TypEq ctx wf (EqTy t0 t1 ty) (EqTy t0' t1' ty')
    TypEqCongEl        : ElEq ctx wf t t' UniverseTy -> TypEq ctx wf (El t) (El t')
    -- Injectivity of type constructors (return TypEq, so they live here)
    TypEqInjPiL        : TypEq ctx wf (PiTy ty1 ty2) (PiTy ty1' ty2') -> TypEq ctx wf ty1 ty1'
    TypEqInjPiR        : (ty1wf : TypWf ctx wf ty1)
                       -> TypEq ctx wf (PiTy ty1 ty2) (PiTy ty1' ty2')
                       -> TypEq (ctx :< ty1) (CtxExt ty1wf) ty2 ty2'
    TypEqInjSigmaL     : TypEq ctx wf (SigmaTy ty1 ty2) (SigmaTy ty1' ty2') -> TypEq ctx wf ty1 ty1'
    TypEqInjSigmaR     : (ty1wf : TypWf ctx wf ty1)
                       -> TypEq ctx wf (SigmaTy ty1 ty2) (SigmaTy ty1' ty2')
                       -> TypEq (ctx :< ty1) (CtxExt ty1wf) ty2 ty2'
    TypEqInjEqTyTy     : TypEq ctx wf (EqTy t0 t1 ty) (EqTy t0' t1' ty') -> TypEq ctx wf ty ty'
    -- Injectivity of context extension and telescope extension → conclude TypEq
    CtxExtInjTy        : CtxEq (ctx1 :< ty) (CtxExt tywf1) (ctx2 :< ty') (CtxExt tywf2)
                       -> TypEq ctx1 wf1 ty ty'
    TelExtInjTy        : TelEq ctx wf (ty1 :: tel1) (ty2 :: tel2) -> TypEq ctx wf ty1 ty2

  ||| Γ ⊦ Δ tel  (indexed by CtxWf ctx)
  public export
  data TelWf : (ctx : Ctx) -> CtxWf ctx -> Tel -> Type where
    TelWfEmpty   : TelWf ctx wf []
    TelWfExt     : (tywf : TypWf ctx wf ty) -> TelWf (ctx :< ty) (CtxExt tywf) tel
                 -> TelWf ctx wf (ty :: tel)
    TelWfSubst   : SubstWf s ctx0 wf0 ctx1 wf1 -> TelWf ctx1 wf1 tel
                 -> TelWf ctx0 wf0 (Tel.subst tel s)
    TelWfConvCtx : TelWf ctx wf tel -> CtxEq ctx wf ctx' wf' -> TelWf ctx' wf' tel

  ||| Γ ⊦ Δ = Δ' tel  (indexed by CtxWf ctx)
  public export
  data TelEq : (ctx : Ctx) -> CtxWf ctx -> Tel -> Tel -> Type where
    TelEqRefl      : TelWf ctx wf tel -> TelEq ctx wf tel tel
    TelEqSym       : TelEq ctx wf tel1 tel2 -> TelEq ctx wf tel2 tel1
    TelEqTrans     : TelEq ctx wf tel1 tel2 -> TelEq ctx wf tel2 tel3 -> TelEq ctx wf tel1 tel3
    TelEqConvCtx   : TelEq ctx wf tel1 tel2 -> CtxEq ctx wf ctx' wf' -> TelEq ctx' wf' tel1 tel2
    -- Congruence
    TelEqCongExt   : (ty1wf : TypWf ctx wf ty1) -> TypEq ctx wf ty1 ty2
                   -> TelEq (ctx :< ty1) (CtxExt ty1wf) tel1 tel2
                   -> TelEq ctx wf (ty1 :: tel1) (ty2 :: tel2)
    TelEqCongSubst : TelEq ctx1 wf1 tel1 tel2 -> SubstEq s s' ctx0 wf0 ctx1 wf1
                   -> TelEq ctx0 wf0 (Tel.subst tel1 s) (Tel.subst tel2 s')
    -- Injectivity
    TelExtInjTel   : (ty1wf : TypWf ctx wf ty1) -> TelEq ctx wf (ty1 :: tel1) (ty2 :: tel2)
                   -> TelEq (ctx :< ty1) (CtxExt ty1wf) tel1 tel2

  ||| Γ ⊦ a : A  (indexed by CtxWf ctx)
  public export
  data ElWf : (ctx : Ctx) -> CtxWf ctx -> Elem -> Typ -> Type where
    -- Universe codes
    ElWfZeroCode  : ElWf ctx wf ZeroTy UniverseTy
    ElWfOneCode   : ElWf ctx wf OneTy UniverseTy
    ElWfNatCode   : ElWf ctx wf NatTy UniverseTy
    ElWfPiCode    : (awf : ElWf ctx wf a UniverseTy)
                  -> ElWf (ctx :< El a) (CtxExt (TypWfEl awf)) b UniverseTy
                  -> ElWf ctx wf (PiTy a b) UniverseTy
    ElWfSigmaCode : (awf : ElWf ctx wf a UniverseTy)
                  -> ElWf (ctx :< El a) (CtxExt (TypWfEl awf)) b UniverseTy
                  -> ElWf ctx wf (SigmaTy a b) UniverseTy
    ElWfEqCode    : ElWf ctx wf a UniverseTy -> ElWf ctx wf t0 (El a) -> ElWf ctx wf t1 (El a)
                  -> ElWf ctx wf (EqTy t0 t1 a) UniverseTy
    -- Canonical elements
    ElWfOneIntro  : ElWf ctx wf OneIntro OneTy
    ElWfZeroIntro : ElWf ctx wf NatIntro0 NatTy
    ElWfSucc      : ElWf ctx wf t NatTy -> ElWf ctx wf (NatIntro1 t) NatTy
    ElWfLam       : (ty1wf : TypWf ctx wf ty1) -> ElWf (ctx :< ty1) (CtxExt ty1wf) f ty2
                  -> ElWf ctx wf (PiIntro f) (PiTy ty1 ty2)
    ElWfApp       : ElWf ctx wf f (PiTy ty1 ty2) -> ElWf ctx wf e ty1
                  -> ElWf ctx wf (PiElim f e) (SubstElim ty2 (Ext Id e))
    ElWfPair      : ElWf ctx wf a ty1 -> ElWf ctx wf b (SubstElim ty2 (Ext Id a))
                  -> ElWf ctx wf (SigmaIntro a b) (SigmaTy ty1 ty2)
    ElWfFst       : ElWf ctx wf t (SigmaTy ty1 ty2) -> ElWf ctx wf (SigmaElim1 t) ty1
    ElWfSnd       : ElWf ctx wf t (SigmaTy ty1 ty2)
                  -> ElWf ctx wf (SigmaElim2 t) (SubstElim ty2 (Ext Id (SigmaElim1 t)))
    ElWfRefl      : ElWf ctx wf t ty -> ElWf ctx wf Refl (EqTy t t ty)
    ElWfZeroElim  : TypWf ctx wf ty -> ElWf ctx wf t ZeroTy -> ElWf ctx wf (ZeroElim t) ty
    ElWfNatElim   : (mwf : TypWf (ctx :< NatTy) (CtxExt TypWfNat) motive)
                  -> ElWf ctx wf z (SubstElim motive (Ext Id NatIntro0))
                  -> ElWf (ctx :< NatTy :< motive) (CtxExt mwf) s
                          (SubstElim motive (Ext Wk (NatIntro1 (CtxVar 0))))
                  -> ElWf ctx wf t NatTy
                  -> ElWf ctx wf (NatElim motive z s t) (SubstElim motive (Ext Id t))
    -- Variable: HasVar captures position and type
    ElWfVar       : HasVar ctx i ty -> ElWf ctx wf (CtxVar i) (SubstElim ty (wkN (S i)))
    -- Substitution
    ElWfSubst     : ElWf ctx1 wf1 t ty -> SubstWf s ctx0 wf0 ctx1 wf1
                  -> ElWf ctx0 wf0 (SubstElim t s) (SubstElim ty s)
    -- Conversion
    ElWfConvTy    : ElWf ctx wf t ty -> TypEq ctx wf ty ty' -> ElWf ctx wf t ty'
    ElWfConvCtx   : ElWf ctx wf t ty -> CtxEq ctx wf ctx' wf' -> ElWf ctx' wf' t ty

  ||| Γ ⊦ a = b : A  (indexed by CtxWf ctx)
  public export
  data ElEq : (ctx : Ctx) -> CtxWf ctx -> Elem -> Elem -> Typ -> Type where
    -- Structural
    ElEqRefl    : ElWf ctx wf t ty -> ElEq ctx wf t t ty
    ElEqSym     : ElEq ctx wf t t' ty -> ElEq ctx wf t' t ty
    ElEqTrans   : ElEq ctx wf t t' ty -> ElEq ctx wf t' t'' ty -> ElEq ctx wf t t'' ty
    ElEqConvTy  : ElEq ctx wf t t' ty -> TypEq ctx wf ty ty' -> ElEq ctx wf t t' ty'
    ElEqConvCtx : ElEq ctx wf t t' ty -> CtxEq ctx wf ctx' wf' -> ElEq ctx' wf' t t' ty
    -- Substitution equalities for elements
    ElEqSubstId        : ElWf ctx wf t ty -> ElEq ctx wf (SubstElim t Id) t ty
    ElEqSubstComp      : ElWf ctx2 wf2 t ty -> SubstWf s ctx1 wf1 ctx2 wf2 -> SubstWf tau ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim (SubstElim t s) tau) (SubstElim t (Chain s tau))
                                (SubstElim ty (Chain s tau))
    ElEqSubstOneIntro  : SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim OneIntro s) OneIntro OneTy
    ElEqSubstZeroIntro : SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim NatIntro0 s) NatIntro0 NatTy
    ElEqSubstSucc      : ElWf ctx1 wf1 t NatTy -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim (NatIntro1 t) s) (NatIntro1 (SubstElim t s)) NatTy
    ElEqSubstZeroCode  : SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim ZeroTy s) ZeroTy UniverseTy
    ElEqSubstOneCode   : SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim OneTy s) OneTy UniverseTy
    ElEqSubstNatCode   : SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim NatTy s) NatTy UniverseTy
    ElEqSubstPiCode    : (awf : ElWf ctx1 wf1 a UniverseTy)
                       -> ElWf (ctx1 :< El a) (CtxExt (TypWfEl awf)) b UniverseTy
                       -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim (PiTy a b) s)
                                        (PiTy (SubstElim a s) (SubstElim b (Under s)))
                                        UniverseTy
    ElEqSubstSigmaCode : (awf : ElWf ctx1 wf1 a UniverseTy)
                       -> ElWf (ctx1 :< El a) (CtxExt (TypWfEl awf)) b UniverseTy
                       -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim (SigmaTy a b) s)
                                        (SigmaTy (SubstElim a s) (SubstElim b (Under s)))
                                        UniverseTy
    ElEqSubstEqCode    : ElWf ctx1 wf1 a UniverseTy -> ElWf ctx1 wf1 t0 (El a) -> ElWf ctx1 wf1 t1 (El a)
                       -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim (EqTy t0 t1 a) s)
                                        (EqTy (SubstElim t0 s) (SubstElim t1 s) (SubstElim a s))
                                        UniverseTy
    ElEqSubstLam       : (ty1wf : TypWf ctx1 wf1 ty1)
                       -> ElWf (ctx1 :< ty1) (CtxExt ty1wf) f ty2
                       -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim (PiIntro f) s)
                                        (PiIntro (SubstElim f (Under s)))
                                        (PiTy (SubstElim ty1 s) (SubstElim ty2 (Under s)))
    ElEqSubstApp       : ElWf ctx1 wf1 f (PiTy ty1 ty2) -> ElWf ctx1 wf1 e ty1
                       -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim (PiElim f e) s)
                                        (PiElim (SubstElim f s) (SubstElim e s))
                                        (SubstElim ty2 (Ext s (SubstElim e s)))
    ElEqSubstPair      : ElWf ctx1 wf1 a ty1 -> ElWf ctx1 wf1 b (SubstElim ty2 (Ext Id a))
                       -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim (SigmaIntro a b) s)
                                        (SigmaIntro (SubstElim a s) (SubstElim b s))
                                        (SigmaTy (SubstElim ty1 s) (SubstElim ty2 (Under s)))
    ElEqSubstFst       : ElWf ctx1 wf1 t (SigmaTy ty1 ty2) -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim (SigmaElim1 t) s)
                                        (SigmaElim1 (SubstElim t s))
                                        (SubstElim ty1 s)
    ElEqSubstSnd       : ElWf ctx1 wf1 t (SigmaTy ty1 ty2) -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim (SigmaElim2 t) s)
                                        (SigmaElim2 (SubstElim t s))
                                        (SubstElim ty2 (Ext s (SigmaElim1 (SubstElim t s))))
    ElEqSubstRefl      : ElWf ctx1 wf1 a ty -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim Refl s)
                                        Refl
                                        (EqTy (SubstElim a s) (SubstElim a s) (SubstElim ty s))
    ElEqSubstZeroElim  : TypWf ctx1 wf1 ty -> ElWf ctx1 wf1 t ZeroTy -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim (ZeroElim t) s)
                                        (ZeroElim (SubstElim t s))
                                        (SubstElim ty s)
    ElEqSubstNatElim   : (mwf : TypWf (ctx1 :< NatTy) (CtxExt TypWfNat) motive)
                       -> ElWf ctx1 wf1 z (SubstElim motive (Ext Id NatIntro0))
                       -> ElWf (ctx1 :< NatTy :< motive) (CtxExt mwf) step
                               (SubstElim motive (Ext Wk (NatIntro1 (CtxVar 0))))
                       -> ElWf ctx1 wf1 t NatTy -> SubstWf s ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim (NatElim motive z step t) s)
                                        (NatElim (SubstElim motive (Under s))
                                                 (SubstElim z s)
                                                 (SubstElim step (Under (Under s)))
                                                 (SubstElim t s))
                                        (SubstElim motive (Ext s (SubstElim t s)))
    -- β/η rules
    ElEqOneEta     : ElWf ctx wf t OneTy -> ElEq ctx wf t OneIntro OneTy
    ElEqPiBeta     : (ty1wf : TypWf ctx wf ty1) -> ElWf (ctx :< ty1) (CtxExt ty1wf) f ty2
                   -> ElWf ctx wf e ty1
                   -> ElEq ctx wf (PiElim (PiIntro f) e) (SubstElim f (Ext Id e))
                            (SubstElim ty2 (Ext Id e))
    ElEqPiEta      : ElWf ctx wf f (PiTy ty1 ty2)
                   -> ElEq ctx wf (PiIntro (PiElim (SubstElim f Wk) (CtxVar 0))) f (PiTy ty1 ty2)
    ElEqSigmaBeta1 : (ty2wf : TypWf (ctx :< ty1) (CtxExt ty1wf) ty2)
                   -> ElWf ctx wf a ty1 -> ElWf ctx wf b (SubstElim ty2 (Ext Id a))
                   -> ElEq ctx wf (SigmaElim1 (SigmaIntro a b)) a ty1
    ElEqSigmaBeta2 : (ty2wf : TypWf (ctx :< ty1) (CtxExt ty1wf) ty2)
                   -> ElWf ctx wf a ty1 -> ElWf ctx wf b (SubstElim ty2 (Ext Id a))
                   -> ElEq ctx wf (SigmaElim2 (SigmaIntro a b)) b (SubstElim ty2 (Ext Id a))
    ElEqSigmaEta   : ElWf ctx wf t (SigmaTy ty1 ty2)
                   -> ElEq ctx wf (SigmaIntro (SigmaElim1 t) (SigmaElim2 t)) t (SigmaTy ty1 ty2)
    -- Variable computation rules
    ElEqVar0   : TypWf ctx1 wf1 ty -> SubstWf s ctx0 wf0 ctx1 wf1 -> ElWf ctx0 wf0 t (SubstElim ty s)
               -> ElEq ctx0 wf0 (SubstElim (CtxVar 0) (Ext s t)) t (SubstElim ty s)
    ElEqVarWk  : HasVar ctx i ty -> (btywf : TypWf ctx wf bty)
               -> ElEq (ctx :< bty) (CtxExt btywf)
                        (SubstElim (CtxVar i) Wk)
                        (CtxVar (S i))
                        (SubstElim ty (wkN (S (S i))))
    -- ℕ-elim β rules
    ElEqNatBeta0 : (mwf : TypWf (ctx :< NatTy) (CtxExt TypWfNat) motive)
                 -> ElWf ctx wf z (SubstElim motive (Ext Id NatIntro0))
                 -> ElWf (ctx :< NatTy :< motive) (CtxExt mwf) step
                          (SubstElim motive (Ext Wk (NatIntro1 (CtxVar 0))))
                 -> ElEq ctx wf (NatElim motive z step NatIntro0) z
                          (SubstElim motive (Ext Id NatIntro0))
    ElEqNatBeta1 : (mwf : TypWf (ctx :< NatTy) (CtxExt TypWfNat) motive)
                 -> ElWf ctx wf z (SubstElim motive (Ext Id NatIntro0))
                 -> ElWf (ctx :< NatTy :< motive) (CtxExt mwf) step
                          (SubstElim motive (Ext Wk (NatIntro1 (CtxVar 0))))
                 -> ElWf ctx wf t NatTy
                 -> ElEq ctx wf (NatElim motive z step (NatIntro1 t))
                          (SubstElim step (Ext (Ext Id t) (NatElim motive z step t)))
                          (SubstElim motive (Ext Id (NatIntro1 t)))
    -- Equality reflection
    ElEqReflection : ElWf ctx wf a (EqTy t0 t1 ty) -> ElEq ctx wf t0 t1 ty
    -- Congruence for element constructors
    ElEqCongSubst      : ElEq ctx1 wf1 t t' ty -> SubstEq s s' ctx0 wf0 ctx1 wf1
                       -> ElEq ctx0 wf0 (SubstElim t s) (SubstElim t' s') (SubstElim ty s)
    ElEqCongLam        : (ty1wf : TypWf ctx wf ty1)
                       -> ElEq (ctx :< ty1) (CtxExt ty1wf) f f' ty2
                       -> ElEq ctx wf (PiIntro f) (PiIntro f') (PiTy ty1 ty2)
    ElEqCongApp        : ElEq ctx wf f f' (PiTy ty1 ty2) -> ElEq ctx wf e e' ty1
                       -> ElEq ctx wf (PiElim f e) (PiElim f' e') (SubstElim ty2 (Ext Id e))
    ElEqCongPair       : ElEq ctx wf a a' ty1 -> ElEq ctx wf b b' (SubstElim ty2 (Ext Id a))
                       -> ElEq ctx wf (SigmaIntro a b) (SigmaIntro a' b') (SigmaTy ty1 ty2)
    ElEqCongFst        : ElEq ctx wf t t' (SigmaTy ty1 ty2)
                       -> ElEq ctx wf (SigmaElim1 t) (SigmaElim1 t') ty1
    ElEqCongSnd        : ElEq ctx wf t t' (SigmaTy ty1 ty2)
                       -> ElEq ctx wf (SigmaElim2 t) (SigmaElim2 t')
                                (SubstElim ty2 (Ext Id (SigmaElim1 t)))
    ElEqCongSucc       : ElEq ctx wf t t' NatTy -> ElEq ctx wf (NatIntro1 t) (NatIntro1 t') NatTy
    ElEqCongNatElim    : (mwf : TypWf (ctx :< NatTy) (CtxExt TypWfNat) motive)
                       -> TypEq (ctx :< NatTy) (CtxExt TypWfNat) motive motive'
                       -> ElEq ctx wf z z' (SubstElim motive (Ext Id NatIntro0))
                       -> ElEq (ctx :< NatTy :< motive) (CtxExt mwf) step step'
                                (SubstElim motive (Ext Wk (NatIntro1 (CtxVar 0))))
                       -> ElEq ctx wf t t' NatTy
                       -> ElEq ctx wf (NatElim motive z step t) (NatElim motive' z' step' t')
                                (SubstElim motive (Ext Id t))
    ElEqCongZeroElim   : TypWf ctx wf ty -> ElEq ctx wf t t' ZeroTy
                       -> ElEq ctx wf (ZeroElim t) (ZeroElim t') ty
    ElEqCongPiCode     : (awf : ElWf ctx wf a UniverseTy) -> ElEq ctx wf a a' UniverseTy
                       -> ElEq (ctx :< El a) (CtxExt (TypWfEl awf)) b b' UniverseTy
                       -> ElEq ctx wf (PiTy a b) (PiTy a' b') UniverseTy
    ElEqCongSigmaCode  : (awf : ElWf ctx wf a UniverseTy) -> ElEq ctx wf a a' UniverseTy
                       -> ElEq (ctx :< El a) (CtxExt (TypWfEl awf)) b b' UniverseTy
                       -> ElEq ctx wf (SigmaTy a b) (SigmaTy a' b') UniverseTy
    ElEqCongEqCode     : ElEq ctx wf t0 t0' (El a) -> ElEq ctx wf t1 t1' (El a)
                       -> ElEq ctx wf a a' UniverseTy
                       -> ElEq ctx wf (EqTy t0 t1 a) (EqTy t0' t1' a') UniverseTy
    -- Injectivity of successor and universe codes
    ElEqInjSucc        : ElEq ctx wf (NatIntro1 t) (NatIntro1 t') NatTy -> ElEq ctx wf t t' NatTy
    ElEqInjPiCodeL     : ElEq ctx wf (PiTy a b) (PiTy a' b') UniverseTy -> ElEq ctx wf a a' UniverseTy
    ElEqInjPiCodeR     : (awf : ElWf ctx wf a UniverseTy)
                       -> ElEq ctx wf (PiTy a b) (PiTy a' b') UniverseTy
                       -> ElEq (ctx :< El a) (CtxExt (TypWfEl awf)) b b' UniverseTy
    ElEqInjSigmaCodeL  : ElEq ctx wf (SigmaTy a b) (SigmaTy a' b') UniverseTy
                       -> ElEq ctx wf a a' UniverseTy
    ElEqInjSigmaCodeR  : (awf : ElWf ctx wf a UniverseTy)
                       -> ElEq ctx wf (SigmaTy a b) (SigmaTy a' b') UniverseTy
                       -> ElEq (ctx :< El a) (CtxExt (TypWfEl awf)) b b' UniverseTy
    ElEqInjEqCodeTy    : ElEq ctx wf (EqTy t0 t1 a) (EqTy t0' t1' a') UniverseTy
                       -> ElEq ctx wf a a' UniverseTy
    ElEqInjEqCodeL     : ElEq ctx wf (EqTy t0 t1 a) (EqTy t0' t1' a') UniverseTy
                       -> ElEq ctx wf t0 t0' (El a)
    ElEqInjEqCodeR     : ElEq ctx wf (EqTy t0 t1 a) (EqTy t0' t1' a') UniverseTy
                       -> ElEq ctx wf t1 t1' (El a)
    -- Injectivity of EqTy and El type constructors → conclude ElEq
    EqTyInjL   : TypEq ctx wf (EqTy t0 t1 ty) (EqTy t0' t1' ty') -> ElEq ctx wf t0 t0' ty
    EqTyInjR   : TypEq ctx wf (EqTy t0 t1 ty) (EqTy t0' t1' ty') -> ElEq ctx wf t1 t1' ty
    ElTypInjEl : TypEq ctx wf (El t) (El t') -> ElEq ctx wf t t' UniverseTy
    -- Injectivity of element list head → conclude ElEq
    ElListInjHead : ElListEq ctx wf (e :: es) (e' :: es') (ty :: tel) -> ElEq ctx wf e e' ty

  ||| Γ ⊦ ē : Δ  (indexed by CtxWf ctx)
  public export
  data ElListWf : (ctx : Ctx) -> CtxWf ctx -> ElemList -> Tel -> Type where
    ElListWfNil     : ElListWf ctx wf [] []
    ElListWfCons    : TelWf ctx wf tel -> ElWf ctx wf e ty
                    -> ElListWf ctx wf es (Tel.subst tel (Ext Id e))
                    -> ElListWf ctx wf (e :: es) (ty :: tel)
    ElListWfSubst   : TelWf ctx1 wf1 tel -> ElListWf ctx1 wf1 es tel -> SubstWf s ctx0 wf0 ctx1 wf1
                    -> ElListWf ctx0 wf0 (ElemList.subst es s) (Tel.subst tel s)
    ElListWfConvCtx : ElListWf ctx wf es tel -> CtxEq ctx wf ctx' wf' -> ElListWf ctx' wf' es tel
    ElListWfConvTel : ElListWf ctx wf es tel -> TelEq ctx wf tel tel' -> ElListWf ctx wf es tel'

  ||| Γ ⊦ ē = ē' : Δ  (indexed by CtxWf ctx)
  public export
  data ElListEq : (ctx : Ctx) -> CtxWf ctx -> ElemList -> ElemList -> Tel -> Type where
    ElListEqRefl      : ElListWf ctx wf es tel -> ElListEq ctx wf es es tel
    ElListEqSym       : ElListEq ctx wf es es' tel -> ElListEq ctx wf es' es tel
    ElListEqTrans     : ElListEq ctx wf es es' tel -> ElListEq ctx wf es' es'' tel
                      -> ElListEq ctx wf es es'' tel
    ElListEqConvCtx   : ElListEq ctx wf es es' tel -> CtxEq ctx wf ctx' wf'
                      -> ElListEq ctx' wf' es es' tel
    ElListEqConvTel   : ElListEq ctx wf es es' tel -> TelEq ctx wf tel tel'
                      -> ElListEq ctx wf es es' tel'
    ElListEqNil       : ElListEq ctx wf [] [] []
    ElListEqCons      : ElEq ctx wf e0 e1 ty
                      -> ElListEq ctx wf es0 es1 (Tel.subst tel (Ext Id e0))
                      -> ElListEq ctx wf (e0 :: es0) (e1 :: es1) (ty :: tel)
    ElListEqCongSubst : ElListEq ctx1 wf1 es es' tel -> SubstEq s s' ctx0 wf0 ctx1 wf1
                      -> ElListEq ctx0 wf0 (ElemList.subst es s)
                                           (ElemList.subst es' s')
                                           (Tel.subst tel s)
    ElListInjTail     : ElListEq ctx wf (e :: es) (e' :: es') (ty :: tel)
                      -> ElListEq ctx wf es es' (Tel.subst tel (Ext Id e))


-- Trivial projections: admissibility of CtxWf becomes a projection

public export
typWfCtxWf : {wf : CtxWf ctx} -> TypWf ctx wf ty -> CtxWf ctx
typWfCtxWf {wf} _ = wf

public export
elWfCtxWf : {wf : CtxWf ctx} -> ElWf ctx wf e ty -> CtxWf ctx
elWfCtxWf {wf} _ = wf

public export
substWfSrcCtxWf : {wf0 : CtxWf ctx0} -> SubstWf s ctx0 wf0 ctx1 wf1 -> CtxWf ctx0
substWfSrcCtxWf {wf0} _ = wf0

public export
substWfTgtCtxWf : {wf1 : CtxWf ctx1} -> SubstWf s ctx0 wf0 ctx1 wf1 -> CtxWf ctx1
substWfTgtCtxWf {wf1} _ = wf1

public export
ctxEqCtxWfLeft : {wf1 : CtxWf ctx1} -> CtxEq ctx1 wf1 ctx2 wf2 -> CtxWf ctx1
ctxEqCtxWfLeft {wf1} _ = wf1

public export
ctxEqCtxWfRight : {wf2 : CtxWf ctx2} -> CtxEq ctx1 wf1 ctx2 wf2 -> CtxWf ctx2
ctxEqCtxWfRight {wf2} _ = wf2

public export
typEqCtxWf : {wf : CtxWf ctx} -> TypEq ctx wf ty ty' -> CtxWf ctx
typEqCtxWf {wf} _ = wf

public export
elEqCtxWf : {wf : CtxWf ctx} -> ElEq ctx wf e e' ty -> CtxWf ctx
elEqCtxWf {wf} _ = wf

public export
telWfCtxWf : {wf : CtxWf ctx} -> TelWf ctx wf tel -> CtxWf ctx
telWfCtxWf {wf} _ = wf

public export
telEqCtxWf : {wf : CtxWf ctx} -> TelEq ctx wf tel tel' -> CtxWf ctx
telEqCtxWf {wf} _ = wf


-- Admissibility: substitution preserves well-formedness
-- (the non-trivial ones that still require induction)

mutual
  public export
  typWfSubst : {sigma, ty : _} -> SubstWf sigma ctx0 wf0 ctx1 wf1 -> TypWf ctx1 wf1 ty -> TypWf ctx0 wf0 (subst ty sigma)
  typWfSubst {sigma, ty = UniverseTy} subwf _ = TypWfUniverse
  typWfSubst {sigma, ty = ZeroTy}     subwf _ = TypWfZero
  typWfSubst {sigma, ty = OneTy}      subwf _ = TypWfOne
  typWfSubst {sigma, ty = NatTy}      subwf _ = TypWfNat
  typWfSubst {sigma, ty = El x} subwf typwf = ?typWfSubst_el
  typWfSubst {sigma, ty = PiTy ty1 ty2} subwf typwf = ?typWfSubst_pi
  typWfSubst {sigma, ty = SigmaTy ty1 ty2} subwf typwf = ?typWfSubst_sigma
  typWfSubst {sigma, ty = EqTy t0 t1 ty} subwf typwf = ?typWfSubst_eqty
  typWfSubst {sigma, ty = SubstElim ty' s} subwf typwf = ?typWfSubst_substElim

  public export
  elWfSubst : {sigma, e, ty : _} -> SubstWf sigma ctx0 wf0 ctx1 wf1
           -> TypWf ctx1 wf1 ty
           -> ElWf ctx1 wf1 e ty
           -> ElWf ctx0 wf0 (subst e sigma) (subst ty sigma)
  elWfSubst subwf tywf elwf = ?elWfSubst_rhs
