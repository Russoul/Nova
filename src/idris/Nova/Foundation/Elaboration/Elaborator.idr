module Nova.Foundation.Elaboration.Elaborator

-- Elaborates the proof-term surface syntax (Nova.Foundation.Elaboration.Syntax)
-- directly into the checked, low-level object language
-- (Nova.Foundation.Syntax) — bypassing Nova.Foundation.Derivation's
-- TypingRule/Truth/generate machinery entirely.
--
-- Every elaborateX is in *check* mode: it is given its "indices" as already
-- well-formed low-level values, and only has to verify/build the value
-- itself, never infer an index. Every judgement in NovaFoundation.txt starts
-- with the "Σ sig" premise, so every elaborateX below is additionally given
-- the ambient Sig, assumed already well-formed (never re-checked here):
--   elaborateCtx     : given a well-formed Sig; assumes nothing else
--   elaborateCtxEq   : given a well-formed Sig and both Ctx's it relates
--   elaborateTy      : given a well-formed Sig and Ctx
--   elaborateTyEq    : given a well-formed Sig and Ctx, and both Ty's
--   elaborateSub     : given a well-formed Sig, and the domain/codomain Ctx's
--   elaborateSubNorm : given a well-formed Sig, and the domain/codomain Ctx's
--   elaborateElem    : given a well-formed Sig and Ctx, and the Ty checked against
--   elaborateElemEq  : given a well-formed Sig and Ctx, the Ty, and both Elem's
-- Equality checks throughout are syntactic (`==`), never up-to-computation.
--
-- All nine sorts (Ctx, CtxEq, Ty, TyEq, Sub, SubNorm, Elem, ElemEq,
-- SubNormEq) are fully implemented below, including Elem.Var/ElemEq.Var/
-- ElemEq.Unfold (signature variables, resolved via the threaded Sig).
--
-- elaborateSig is the top-level entry point: unlike every other elaborateX,
-- it takes no ambient Sig — Σ ::= ε | Σ (Γ ⊦ x ≔ a : A) is the root
-- judgement everything else's "Σ sig" premise ultimately bottoms out at.
-- It builds Σ up incrementally via elaborateSigEntry, checking each new
-- entry's x ∉ Σ against the prefix already elaborated so far (which is
-- exactly what the "x ∉ Σ" premise means, one entry at a time).

import Data.SnocList
import Nova.Foundation.Subst
import Nova.Foundation.Syntax as Low
import Nova.Foundation.Elaboration.Syntax as Surface

%default covering

public export
data ElabError : Type where
  ||| Placeholder for elaborator pieces not implemented yet.
  NotYetSupported : String -> ElabError
  ||| Two Ctx's were expected to be (syntactically) equal but weren't.
  CtxMismatch : Low.Ctx -> Low.Ctx -> ElabError
  ||| A Ctx was expected to be of the form (Γ ᐅ A) but wasn't.
  NotACtxExtension : Low.Ctx -> ElabError
  ||| Two Ty's were expected to be (syntactically) equal but weren't.
  TyMismatch : Low.Ty.Ty -> Low.Ty.Ty -> ElabError
  ||| Two Elem's were expected to be (syntactically) equal but weren't.
  ElemMismatch : Low.Elem.Elem -> Low.Elem.Elem -> ElabError
  ||| A Ty was expected to be of a specific shape (e.g. "_ → _") but wasn't.
  UnexpectedTyShape : String -> Low.Ty.Ty -> ElabError
  ||| ☐ₙ has no corresponding entry in Γ.
  CtxVarOutOfBounds : Low.Ctx -> Nat -> ElabError
  ||| x[e˲] refers to a signature identifier not present in Σ.
  SigIdentifierNotFound : Low.SigIdentifier -> ElabError
  ||| An Elem was expected to be of a specific shape (e.g. "_ , _") but wasn't.
  UnexpectedElemShape : String -> Low.Elem.Elem -> ElabError
  ||| Two SubNorm's were expected to be (syntactically) equal but weren't.
  SubNormMismatch : Low.SubNorm -> Low.SubNorm -> ElabError
  ||| A SigEntry's identifier x is already defined earlier in Σ.
  SigIdentifierAlreadyDefined : Low.SigIdentifier -> ElabError

export
covering
Show ElabError where
  show (NotYetSupported msg) = "NotYetSupported \{show msg}"
  show (CtxMismatch g0 g1) = "CtxMismatch (\{show g0}) (\{show g1})"
  show (NotACtxExtension g) = "NotACtxExtension (\{show g})"
  show (TyMismatch t0 t1) = "TyMismatch (\{show t0}) (\{show t1})"
  show (ElemMismatch e0 e1) = "ElemMismatch (\{show e0}) (\{show e1})"
  show (UnexpectedTyShape desc t) = "UnexpectedTyShape \{show desc} (\{show t})"
  show (CtxVarOutOfBounds g n) = "CtxVarOutOfBounds (\{show g}) \{show n}"
  show (SigIdentifierNotFound x) = "SigIdentifierNotFound \{show x}"
  show (UnexpectedElemShape desc e) = "UnexpectedElemShape \{show desc} (\{show e})"
  show (SubNormMismatch s0 s1) = "SubNormMismatch (\{show s0}) (\{show s1})"
  show (SigIdentifierAlreadyDefined x) = "SigIdentifierAlreadyDefined \{show x}"

||| Γ‖ₙ: the (n+1)-th type in Γ counting from the right, matching
||| NovaFoundation.txt's (Γ ᐅ A)‖₀ ≜ A[↑], (Γ ᐅ A)‖ₙ₊₁ ≜ Γ‖ₙ[↑].
ctxLookup : Low.Ctx -> Nat -> Maybe Low.Ty.Ty
ctxLookup [<]          _     = Nothing
ctxLookup (rest :< ty) Z     = Just (substTy ty Wk)
ctxLookup (rest :< ty) (S n) = map (\t => substTy t Wk) (ctxLookup rest n)

||| (Γ ⊦ x ≔ a : A) ∈ Σ
sigLookup : Low.SigIdentifier -> Low.Sig -> Maybe Low.SigEntry
sigLookup x [<] = Nothing
sigLookup x (rest :< entry@(_, name, _, _)) =
  if name == x then Just entry else sigLookup x rest

mutual
  ||| Given a well-formed Sig, Γ ::= ε | Γ ᐅ T  (assumes nothing else)
  export
  elaborateCtx : Low.Sig -> Surface.Ctx.Ctx -> Either ElabError Low.Ctx
  elaborateCtx sig Surface.Ctx.Empty = Right [<]
  elaborateCtx sig (Surface.Ctx.Ext g a) = do
    lowG <- elaborateCtx sig g
    lowA <- elaborateTy sig lowG a
    Right (lowG :< lowA)

  ||| Given a well-formed Sig and Ctx, checks a surface Ty relative to it.
  export
  elaborateTy : Low.Sig -> Low.Ctx -> Surface.Ty.Ty -> Either ElabError Low.Ty.Ty
  elaborateTy sig ctx Surface.Ty.ZeroTy     = Right Low.Ty.ZeroTy
  elaborateTy sig ctx Surface.Ty.OneTy      = Right Low.Ty.OneTy
  elaborateTy sig ctx Surface.Ty.NatTy      = Right Low.Ty.NatTy
  elaborateTy sig ctx Surface.Ty.UniverseTy = Right Low.Ty.UniverseTy
  elaborateTy sig ctx (Surface.Ty.PiTy a b) = do
    lowA <- elaborateTy sig ctx a
    lowB <- elaborateTy sig (ctx :< lowA) b
    Right (Low.Ty.PiTy lowA lowB)
  elaborateTy sig ctx (Surface.Ty.SigmaTy a b) = do
    lowA <- elaborateTy sig ctx a
    lowB <- elaborateTy sig (ctx :< lowA) b
    Right (Low.Ty.SigmaTy lowA lowB)
  elaborateTy sig ctx (Surface.Ty.Quotient a r) = do
    lowA <- elaborateTy sig ctx a
    lowR <- elaborateTy sig (ctx :< lowA :< substTy lowA Wk) r
    Right (Low.Ty.Quotient lowA lowR)
  elaborateTy sig ctx (Surface.Ty.EqTy a b t) = do
    lowT <- elaborateTy sig ctx t
    lowA <- elaborateElem sig ctx lowT a
    lowB <- elaborateElem sig ctx lowT b
    Right (Low.Ty.EqTy lowA lowB lowT)
  elaborateTy sig ctx (Surface.Ty.El e) = do
    lowE <- elaborateElem sig ctx Low.Ty.UniverseTy e
    Right (Low.Ty.El lowE)
  elaborateTy sig ctx (Surface.Ty.Subst g a s) = do
    lowG <- elaborateCtx sig g
    lowA <- elaborateTy sig lowG a
    lowS <- elaborateSub sig ctx lowG s
    Right (substTy lowA lowS)
  elaborateTy sig ctx (Surface.Ty.CoeCtx a g geq) = do
    lowG <- elaborateCtx sig g
    lowA <- elaborateTy sig lowG a
    _ <- elaborateCtxEq sig lowG ctx geq
    Right lowA

  ||| Given a well-formed Sig and Ctx, and the Ty it's checked against.
  export
  elaborateElem : Low.Sig -> Low.Ctx -> Low.Ty.Ty -> Surface.Elem.Elem -> Either ElabError Low.Elem.Elem
  elaborateElem sig ctx ty (Elem.CtxVar n) =
    case ctxLookup ctx n of
      Nothing => Left (CtxVarOutOfBounds ctx n)
      Just t  => if t == ty then Right (Low.Elem.CtxVar n) else Left (TyMismatch t ty)
  elaborateElem sig ctx ty Elem.OneIntro =
    if ty == Low.Ty.OneTy then Right Low.Elem.OneIntro else Left (TyMismatch Low.Ty.OneTy ty)
  elaborateElem sig ctx ty Elem.NatIntro0 =
    if ty == Low.Ty.NatTy then Right Low.Elem.NatIntro0 else Left (TyMismatch Low.Ty.NatTy ty)
  elaborateElem sig ctx ty Elem.Refl =
    case ty of
      Low.Ty.EqTy a b _ => if a == b then Right Low.Elem.Refl else Left (ElemMismatch a b)
      _                 => Left (UnexpectedTyShape "_ ≡ _ ∈ _" ty)
  elaborateElem sig ctx ty Elem.ZeroTy =
    if ty == Low.Ty.UniverseTy then Right Low.Elem.ZeroTy else Left (TyMismatch Low.Ty.UniverseTy ty)
  elaborateElem sig ctx ty Elem.OneTy =
    if ty == Low.Ty.UniverseTy then Right Low.Elem.OneTy else Left (TyMismatch Low.Ty.UniverseTy ty)
  elaborateElem sig ctx ty Elem.NatTy =
    if ty == Low.Ty.UniverseTy then Right Low.Elem.NatTy else Left (TyMismatch Low.Ty.UniverseTy ty)
  elaborateElem sig ctx ty (Elem.Var x s) =
    case sigLookup x sig of
      Nothing => Left (SigIdentifierNotFound x)
      Just (gammaX, _, _, bigA) => do
        lowS <- elaborateSubNorm sig ctx gammaX s
        let expected = substTy bigA (embed lowS)
        if expected == ty
          then Right (Low.Elem.SigVar x lowS)
          else Left (TyMismatch expected ty)
  elaborateElem sig ctx ty (Elem.Subst g a e s) = do
    lowG <- elaborateCtx sig g
    lowA <- elaborateTy sig lowG a
    lowS <- elaborateSub sig ctx lowG s
    lowE <- elaborateElem sig lowG lowA e
    let expected = substTy lowA lowS
    if expected == ty
      then Right (substElem lowE lowS)
      else Left (TyMismatch expected ty)
  elaborateElem sig ctx ty (Elem.App f a b e) = do
    lowA <- elaborateTy sig ctx a
    lowB <- elaborateTy sig (ctx :< lowA) b
    lowF <- elaborateElem sig ctx (Low.Ty.PiTy lowA lowB) f
    lowE <- elaborateElem sig ctx lowA e
    let expected = substTy lowB (Ext Id lowE)
    if expected == ty
      then Right (Low.Elem.PiApp lowF lowE)
      else Left (TyMismatch expected ty)
  elaborateElem sig ctx ty (Elem.Proj1 t a b) = do
    lowA <- elaborateTy sig ctx a
    lowB <- elaborateTy sig (ctx :< lowA) b
    lowT <- elaborateElem sig ctx (Low.Ty.SigmaTy lowA lowB) t
    if lowA == ty
      then Right (Low.Elem.SigmaElim1 lowT)
      else Left (TyMismatch lowA ty)
  elaborateElem sig ctx ty (Elem.Proj2 t a b) = do
    lowA <- elaborateTy sig ctx a
    lowB <- elaborateTy sig (ctx :< lowA) b
    lowT <- elaborateElem sig ctx (Low.Ty.SigmaTy lowA lowB) t
    let expected = substTy lowB (Ext Id (Low.Elem.SigmaElim1 lowT))
    if expected == ty
      then Right (Low.Elem.SigmaElim2 lowT)
      else Left (TyMismatch expected ty)
  elaborateElem sig ctx ty (Elem.PiIntro body) =
    case ty of
      Low.Ty.PiTy a b => do
        lowBody <- elaborateElem sig (ctx :< a) b body
        Right (Low.Elem.PiIntro lowBody)
      _ => Left (UnexpectedTyShape "_ → _" ty)
  elaborateElem sig ctx ty (Elem.ZeroElim t) = do
    lowT <- elaborateElem sig ctx Low.Ty.ZeroTy t
    Right (Low.Elem.ZeroElim lowT)
  elaborateElem sig ctx ty (Elem.NatIntro1 t) =
    if ty == Low.Ty.NatTy
      then do
        lowT <- elaborateElem sig ctx Low.Ty.NatTy t
        Right (Low.Elem.NatIntro1 lowT)
      else Left (TyMismatch Low.Ty.NatTy ty)
  elaborateElem sig ctx ty (Elem.NatElim z s t a) = do
    lowA <- elaborateTy sig (ctx :< Low.Ty.NatTy) a
    lowZ <- elaborateElem sig ctx (substTy lowA (Ext Id Low.Elem.NatIntro0)) z
    let sTy = substTy lowA (Chain (Ext Wk (Low.Elem.NatIntro1 (Low.Elem.CtxVar 0))) Wk)
    lowS <- elaborateElem sig (ctx :< Low.Ty.NatTy :< lowA) sTy s
    lowT <- elaborateElem sig ctx Low.Ty.NatTy t
    let expected = substTy lowA (Ext Id lowT)
    if expected == ty
      then Right (Low.Elem.NatElim lowZ lowS lowT)
      else Left (TyMismatch expected ty)
  elaborateElem sig ctx ty (Elem.Class a) =
    case ty of
      Low.Ty.Quotient bigA r => do
        lowA <- elaborateElem sig ctx bigA a
        Right (Low.Elem.Class lowA)
      _ => Left (UnexpectedTyShape "_ / _" ty)
  elaborateElem sig ctx ty (Elem.QuotElim bigA r f fEq q b) = do
    lowA <- elaborateTy sig ctx bigA
    lowR <- elaborateTy sig (ctx :< lowA :< substTy lowA Wk) r
    lowB <- elaborateTy sig (ctx :< Low.Ty.Quotient lowA lowR) b
    let fTy = substTy lowB (Ext Wk (Low.Elem.Class (Low.Elem.CtxVar 0)))
    lowF <- elaborateElem sig (ctx :< lowA) fTy f
    let wk3 = Chain Wk (Chain Wk Wk)
        respCtx = ctx :< lowA :< substTy lowA Wk :< lowR
        lhs = substElem lowF (Ext wk3 (Low.Elem.CtxVar 2))
        rhs = substElem lowF (Ext wk3 (Low.Elem.CtxVar 1))
        respTy = substTy lowB (Ext wk3 (Low.Elem.Class (Low.Elem.CtxVar 2)))
    _ <- elaborateElemEq sig respCtx respTy lhs rhs fEq
    lowQ <- elaborateElem sig ctx (Low.Ty.Quotient lowA lowR) q
    let expected = substTy lowB (Ext Id lowQ)
    if expected == ty
      then Right (Low.Elem.QuotElim lowF lowQ)
      else Left (TyMismatch expected ty)
  elaborateElem sig ctx ty (Elem.CoeCtx a g geq) = do
    lowG <- elaborateCtx sig g
    lowA <- elaborateElem sig lowG ty a
    _ <- elaborateCtxEq sig lowG ctx geq
    Right lowA
  elaborateElem sig ctx ty (Elem.CoeTy a a0 aeq) = do
    lowA0 <- elaborateTy sig ctx a0
    lowA <- elaborateElem sig ctx lowA0 a
    _ <- elaborateTyEq sig ctx lowA0 ty aeq
    Right lowA
  elaborateElem sig ctx ty (Elem.PiTyCode a b) =
    if ty == Low.Ty.UniverseTy
      then do
        lowA <- elaborateElem sig ctx Low.Ty.UniverseTy a
        lowB <- elaborateElem sig (ctx :< Low.Ty.El lowA) Low.Ty.UniverseTy b
        Right (Low.Elem.PiTy lowA lowB)
      else Left (TyMismatch Low.Ty.UniverseTy ty)
  elaborateElem sig ctx ty (Elem.SigmaTyCode a b) =
    if ty == Low.Ty.UniverseTy
      then do
        lowA <- elaborateElem sig ctx Low.Ty.UniverseTy a
        lowB <- elaborateElem sig (ctx :< Low.Ty.El lowA) Low.Ty.UniverseTy b
        Right (Low.Elem.SigmaTy lowA lowB)
      else Left (TyMismatch Low.Ty.UniverseTy ty)
  elaborateElem sig ctx ty (Elem.EqTyCode a0 a1 bigA) =
    if ty == Low.Ty.UniverseTy
      then do
        lowBigA <- elaborateElem sig ctx Low.Ty.UniverseTy bigA
        lowA0 <- elaborateElem sig ctx (Low.Ty.El lowBigA) a0
        lowA1 <- elaborateElem sig ctx (Low.Ty.El lowBigA) a1
        Right (Low.Elem.EqTy lowA0 lowA1 lowBigA)
      else Left (TyMismatch Low.Ty.UniverseTy ty)
  elaborateElem sig ctx ty (Elem.SigmaIntro a b) =
    case ty of
      Low.Ty.SigmaTy bigA bigB => do
        lowA <- elaborateElem sig ctx bigA a
        lowB <- elaborateElem sig ctx (substTy bigB (Ext Id lowA)) b
        Right (Low.Elem.SigmaIntro lowA lowB)
      _ => Left (UnexpectedTyShape "_ ⨯ _" ty)

  ||| Given a well-formed Sig and Ctx, the Ty, and both Elem's it relates.
  export
  elaborateElemEq : Low.Sig -> Low.Ctx -> Low.Ty.Ty -> Low.Elem.Elem -> Low.Elem.Elem -> ElemEq -> Either ElabError ()
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.CtxVar n) =
    if e0 == Low.Elem.CtxVar n && e1 == Low.Elem.CtxVar n
      then Right ()
      else Left (ElemMismatch e0 e1)
  elaborateElemEq sig ctx ty e0 e1 ElemEq.OneIntro =
    if e0 == Low.Elem.OneIntro && e1 == Low.Elem.OneIntro then Right () else Left (ElemMismatch e0 e1)
  elaborateElemEq sig ctx ty e0 e1 ElemEq.NatIntro0 =
    if e0 == Low.Elem.NatIntro0 && e1 == Low.Elem.NatIntro0 then Right () else Left (ElemMismatch e0 e1)
  elaborateElemEq sig ctx ty e0 e1 ElemEq.ZeroTy =
    if e0 == Low.Elem.ZeroTy && e1 == Low.Elem.ZeroTy then Right () else Left (ElemMismatch e0 e1)
  elaborateElemEq sig ctx ty e0 e1 ElemEq.OneTy =
    if e0 == Low.Elem.OneTy && e1 == Low.Elem.OneTy then Right () else Left (ElemMismatch e0 e1)
  elaborateElemEq sig ctx ty e0 e1 ElemEq.NatTy =
    if e0 == Low.Elem.NatTy && e1 == Low.Elem.NatTy then Right () else Left (ElemMismatch e0 e1)
  elaborateElemEq sig ctx ty e0 e1 ElemEq.Refl =
    if e0 == e1 then Right () else Left (ElemMismatch e0 e1)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.Var x) =
    case e0 of
      Low.Elem.SigVar x0 s0 =>
        if x0 == x && e0 == e1 then Right () else Left (ElemMismatch e0 e1)
      _ => Left (UnexpectedElemShape "x[_]" e0)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.Unfold x) =
    case e0 of
      Low.Elem.SigVar x0 s0 =>
        if x0 == x
          then case sigLookup x sig of
                 Nothing => Left (SigIdentifierNotFound x)
                 Just (_, _, defA, _) =>
                   let expected = substElem defA (embed s0) in
                   if expected == e1 then Right () else Left (ElemMismatch expected e1)
          else Left (UnexpectedElemShape "x[_]" e0)
      _ => Left (UnexpectedElemShape "x[_]" e0)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.Sym eeq) =
    elaborateElemEq sig ctx ty e1 e0 eeq
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.Subst g eeq t0 t1 a s) = do
    lowG <- elaborateCtx sig g
    lowA <- elaborateTy sig lowG a
    lowS <- elaborateSub sig ctx lowG s
    lowT0 <- elaborateElem sig lowG lowA t0
    lowT1 <- elaborateElem sig lowG lowA t1
    _ <- elaborateElemEq sig lowG lowA lowT0 lowT1 eeq
    let expectedTy = substTy lowA lowS
        expected0 = substElem lowT0 lowS
        expected1 = substElem lowT1 lowS
    if expectedTy == ty && expected0 == e0 && expected1 == e1
      then Right ()
      else Left (TyMismatch expectedTy ty)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.App fEq a b aEq) =
    case (e0, e1) of
      (Low.Elem.PiApp f0 a0, Low.Elem.PiApp f1 a1) => do
        lowA <- elaborateTy sig ctx a
        lowB <- elaborateTy sig (ctx :< lowA) b
        _ <- elaborateElemEq sig ctx (Low.Ty.PiTy lowA lowB) f0 f1 fEq
        _ <- elaborateElemEq sig ctx lowA a0 a1 aEq
        let expected = substTy lowB (Ext Id a1)
        if expected == ty then Right () else Left (TyMismatch expected ty)
      _ => Left (UnexpectedElemShape "_ _" e0)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.Proj1 tEq a b) =
    case (e0, e1) of
      (Low.Elem.SigmaElim1 t0, Low.Elem.SigmaElim1 t1) => do
        lowA <- elaborateTy sig ctx a
        lowB <- elaborateTy sig (ctx :< lowA) b
        _ <- elaborateElemEq sig ctx (Low.Ty.SigmaTy lowA lowB) t0 t1 tEq
        if lowA == ty then Right () else Left (TyMismatch lowA ty)
      _ => Left (UnexpectedElemShape "_ .π₁" e0)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.Proj2 tEq a b) =
    case (e0, e1) of
      (Low.Elem.SigmaElim2 t0, Low.Elem.SigmaElim2 t1) => do
        lowA <- elaborateTy sig ctx a
        lowB <- elaborateTy sig (ctx :< lowA) b
        _ <- elaborateElemEq sig ctx (Low.Ty.SigmaTy lowA lowB) t0 t1 tEq
        let expected = substTy lowB (Ext Id (Low.Elem.SigmaElim1 t1))
        if expected == ty then Right () else Left (TyMismatch expected ty)
      _ => Left (UnexpectedElemShape "_ .π₂" e0)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.NatIntro1 tEq) =
    case (e0, e1) of
      (Low.Elem.NatIntro1 t0, Low.Elem.NatIntro1 t1) =>
        if ty == Low.Ty.NatTy
          then elaborateElemEq sig ctx Low.Ty.NatTy t0 t1 tEq
          else Left (TyMismatch Low.Ty.NatTy ty)
      _ => Left (UnexpectedElemShape "S _" e0)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.PiIntro bodyEq) =
    case (ty, e0, e1) of
      (Low.Ty.PiTy a b, Low.Elem.PiIntro body0, Low.Elem.PiIntro body1) =>
        elaborateElemEq sig (ctx :< a) b body0 body1 bodyEq
      _ => Left (UnexpectedTyShape "_ → _" ty)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.Class aEq) =
    case (ty, e0, e1) of
      (Low.Ty.Quotient bigA r, Low.Elem.Class a0, Low.Elem.Class a1) =>
        elaborateElemEq sig ctx bigA a0 a1 aEq
      _ => Left (UnexpectedTyShape "_ / _" ty)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.ClassEq r) =
    case (ty, e0, e1) of
      (Low.Ty.Quotient bigA bigR, Low.Elem.Class a, Low.Elem.Class b) => do
        _ <- elaborateElem sig ctx (substTy bigR (Ext (Ext Id a) b)) r
        Right ()
      _ => Left (UnexpectedTyShape "_ / _" ty)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.ZeroElim t) = do
    _ <- elaborateElem sig ctx Low.Ty.ZeroTy t
    Right ()
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.NatElim zEq sEq tEq a) =
    case (e0, e1) of
      (Low.Elem.NatElim z0 s0 t0, Low.Elem.NatElim z1 s1 t1) => do
        lowA <- elaborateTy sig (ctx :< Low.Ty.NatTy) a
        _ <- elaborateElemEq sig ctx (substTy lowA (Ext Id Low.Elem.NatIntro0)) z0 z1 zEq
        let sTy = substTy lowA (Chain (Ext Wk (Low.Elem.NatIntro1 (Low.Elem.CtxVar 0))) Wk)
        _ <- elaborateElemEq sig (ctx :< Low.Ty.NatTy :< lowA) sTy s0 s1 sEq
        _ <- elaborateElemEq sig ctx Low.Ty.NatTy t0 t1 tEq
        let expected = substTy lowA (Ext Id t1)
        if expected == ty then Right () else Left (TyMismatch expected ty)
      _ => Left (UnexpectedElemShape "ℕ-elim _ _ _" e0)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.NatElimEta z s fEq f0Eq f1Eq t f0 f1 a) = do
    lowA <- elaborateTy sig (ctx :< Low.Ty.NatTy) a
    lowF0 <- elaborateElem sig (ctx :< Low.Ty.NatTy) lowA f0
    lowF1 <- elaborateElem sig (ctx :< Low.Ty.NatTy) lowA f1
    lowZ <- elaborateElem sig ctx (substTy lowA (Ext Id Low.Elem.NatIntro0)) z
    let sTy = substTy lowA (Chain (Ext Wk (Low.Elem.NatIntro1 (Low.Elem.CtxVar 0))) Wk)
    lowS <- elaborateElem sig (ctx :< Low.Ty.NatTy :< lowA) sTy s
    let stepSub = Ext Wk (Low.Elem.NatIntro1 (Low.Elem.CtxVar 0))
        fEqTy = substTy lowA (Ext Id Low.Elem.NatIntro0)
    _ <- elaborateElemEq sig ctx fEqTy (substElem lowF0 (Ext Id Low.Elem.NatIntro0)) (substElem lowF1 (Ext Id Low.Elem.NatIntro0)) fEq
    let f0EqTy = substTy lowA stepSub
    _ <- elaborateElemEq sig (ctx :< Low.Ty.NatTy) f0EqTy (substElem lowF0 stepSub) (substElem lowS (Ext Id lowF0)) f0Eq
    _ <- elaborateElemEq sig (ctx :< Low.Ty.NatTy) f0EqTy (substElem lowF1 stepSub) (substElem lowS (Ext Id lowF1)) f1Eq
    lowT <- elaborateElem sig ctx Low.Ty.NatTy t
    let expected = substTy lowA (Ext Id lowT)
        expected0 = substElem lowF0 (Ext Id lowT)
        expected1 = substElem lowF1 (Ext Id lowT)
    if expected == ty && expected0 == e0 && expected1 == e1
      then Right ()
      else Left (TyMismatch expected ty)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.QuotElim bigA r fEq resp0 resp1 qEq b) =
    case (e0, e1) of
      (Low.Elem.QuotElim f0 q0, Low.Elem.QuotElim f1 q1) => do
        lowA <- elaborateTy sig ctx bigA
        lowR <- elaborateTy sig (ctx :< lowA :< substTy lowA Wk) r
        lowB <- elaborateTy sig (ctx :< Low.Ty.Quotient lowA lowR) b
        let fTy = substTy lowB (Ext Wk (Low.Elem.Class (Low.Elem.CtxVar 0)))
        _ <- elaborateElemEq sig (ctx :< lowA) fTy f0 f1 fEq
        let wk3 = Chain Wk (Chain Wk Wk)
            respCtx = ctx :< lowA :< substTy lowA Wk :< lowR
            respTy = substTy lowB (Ext wk3 (Low.Elem.Class (Low.Elem.CtxVar 2)))
        _ <- elaborateElemEq sig respCtx respTy
               (substElem f0 (Ext wk3 (Low.Elem.CtxVar 2))) (substElem f0 (Ext wk3 (Low.Elem.CtxVar 1))) resp0
        _ <- elaborateElemEq sig respCtx respTy
               (substElem f1 (Ext wk3 (Low.Elem.CtxVar 2))) (substElem f1 (Ext wk3 (Low.Elem.CtxVar 1))) resp1
        _ <- elaborateElemEq sig ctx (Low.Ty.Quotient lowA lowR) q0 q1 qEq
        let expected = substTy lowB (Ext Id q1)
        if expected == ty then Right () else Left (TyMismatch expected ty)
      _ => Left (UnexpectedElemShape "quot-elim _ _" e0)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.Reflect t) = do
    _ <- elaborateElem sig ctx (Low.Ty.EqTy e0 e1 ty) t
    Right ()
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.CoeCtx eeq g geq) = do
    lowG <- elaborateCtx sig g
    _ <- elaborateElemEq sig lowG ty e0 e1 eeq
    elaborateCtxEq sig lowG ctx geq
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.CoeTy eeq a0 aeq) = do
    lowA0 <- elaborateTy sig ctx a0
    _ <- elaborateElemEq sig ctx lowA0 e0 e1 eeq
    elaborateTyEq sig ctx lowA0 ty aeq
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.PiTyCode aEq bEq) =
    if ty == Low.Ty.UniverseTy
      then case (e0, e1) of
        (Low.Elem.PiTy a0 b0, Low.Elem.PiTy a1 b1) => do
          _ <- elaborateElemEq sig ctx Low.Ty.UniverseTy a0 a1 aEq
          elaborateElemEq sig (ctx :< Low.Ty.El a1) Low.Ty.UniverseTy b0 b1 bEq
        _ => Left (UnexpectedElemShape "_ → _" e0)
      else Left (TyMismatch Low.Ty.UniverseTy ty)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.SigmaTyCode aEq bEq) =
    if ty == Low.Ty.UniverseTy
      then case (e0, e1) of
        (Low.Elem.SigmaTy a0 b0, Low.Elem.SigmaTy a1 b1) => do
          _ <- elaborateElemEq sig ctx Low.Ty.UniverseTy a0 a1 aEq
          elaborateElemEq sig (ctx :< Low.Ty.El a1) Low.Ty.UniverseTy b0 b1 bEq
        _ => Left (UnexpectedElemShape "_ ⨯ _" e0)
      else Left (TyMismatch Low.Ty.UniverseTy ty)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.EqTyCode aEq bEq cEq) =
    if ty == Low.Ty.UniverseTy
      then case (e0, e1) of
        (Low.Elem.EqTy a0 b0 bigA0, Low.Elem.EqTy a1 b1 bigA1) => do
          _ <- elaborateElemEq sig ctx Low.Ty.UniverseTy bigA0 bigA1 cEq
          _ <- elaborateElemEq sig ctx (Low.Ty.El bigA1) a0 a1 aEq
          elaborateElemEq sig ctx (Low.Ty.El bigA1) b0 b1 bEq
        _ => Left (UnexpectedElemShape "_ ≡ _ ∈ _" e0)
      else Left (TyMismatch Low.Ty.UniverseTy ty)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.SigmaIntro aEq bEq) =
    case (ty, e0, e1) of
      (Low.Ty.SigmaTy bigA bigB, Low.Elem.SigmaIntro a0 b0, Low.Elem.SigmaIntro a1 b1) => do
        _ <- elaborateElemEq sig ctx bigA a0 a1 aEq
        elaborateElemEq sig ctx (substTy bigB (Ext Id a1)) b0 b1 bEq
      _ => Left (UnexpectedTyShape "_ ⨯ _" ty)
  elaborateElemEq sig ctx ty e0 e1 (ElemEq.Trans eeq0 eeq1 midE) = do
    lowMid <- elaborateElem sig ctx ty midE
    _ <- elaborateElemEq sig ctx ty e0 lowMid eeq0
    elaborateElemEq sig ctx ty lowMid e1 eeq1

  ||| Given a well-formed Sig, and the domain and codomain Ctx's —
  ||| σ ::= · | id | ↑ | σ, t | σ ∘ σ via Γ
  export
  elaborateSub : Low.Sig -> Low.Ctx -> Low.Ctx -> Surface.Sub.Sub -> Either ElabError Low.Sub.Sub
  elaborateSub sig dom cod Surface.Sub.Terminal =
    case cod of
      [<] => Right Low.Sub.Terminal
      _   => Left (CtxMismatch [<] cod)
  elaborateSub sig dom cod Surface.Sub.Id =
    if dom == cod
      then Right Low.Sub.Id
      else Left (CtxMismatch dom cod)
  elaborateSub sig dom cod Surface.Sub.Wk =
    case dom of
      (rest :< _) =>
        if rest == cod
          then Right Low.Sub.Wk
          else Left (CtxMismatch rest cod)
      [<] => Left (NotACtxExtension dom)
  elaborateSub sig dom cod (Surface.Sub.Ext s e) =
    case cod of
      (cod' :< a) => do
        lowS <- elaborateSub sig dom cod' s
        lowE <- elaborateElem sig dom (substTy a lowS) e
        Right (Low.Sub.Ext lowS lowE)
      [<] => Left (NotACtxExtension cod)
  elaborateSub sig dom cod (Surface.Sub.Chain s t midG) = do
    lowMidG <- elaborateCtx sig midG
    lowS <- elaborateSub sig dom lowMidG s
    lowT <- elaborateSub sig lowMidG cod t
    Right (Low.Sub.Chain lowS lowT)

  ||| Given a well-formed Sig, and the domain and codomain Ctx's —
  ||| t˲ ::= · | coe-dom t˲ via (Γ, Γ⁼) | coe-codom t˲ via (Γ, Γ⁼) | t˲, t | t˲ ∘ σ via Γ
  export
  elaborateSubNorm : Low.Sig -> Low.Ctx -> Low.Ctx -> Surface.SubNorm.SubNorm -> Either ElabError Low.SubNorm
  elaborateSubNorm sig dom cod SubNorm.Terminal =
    case cod of
      [<] => Right [<]
      _   => Left (CtxMismatch [<] cod)
  elaborateSubNorm sig dom cod (SubNorm.CoeDom s g geq) = do
    lowG <- elaborateCtx sig g
    lowS <- elaborateSubNorm sig lowG cod s
    _ <- elaborateCtxEq sig lowG dom geq
    Right lowS
  elaborateSubNorm sig dom cod (SubNorm.CoeCodom s g geq) = do
    lowG <- elaborateCtx sig g
    lowS <- elaborateSubNorm sig dom lowG s
    _ <- elaborateCtxEq sig lowG cod geq
    Right lowS
  elaborateSubNorm sig dom cod (SubNorm.Ext s e) =
    case cod of
      (delta :< ty) => do
        lowS <- elaborateSubNorm sig dom delta s
        lowE <- elaborateElem sig dom (substTy ty (embed lowS)) e
        Right (lowS :< lowE)
      [<] => Left (NotACtxExtension cod)
  elaborateSubNorm sig dom cod (SubNorm.Chain s t midG) = do
    lowMidG <- elaborateCtx sig midG
    lowS <- elaborateSubNorm sig lowMidG cod s
    lowT <- elaborateSub sig dom lowMidG t
    Right (substSubNorm lowS lowT)

  ||| Given a well-formed Sig, the domain/codomain Ctx's, and both SubNorm's
  ||| it relates — t˲⁼ ::= · | refl | t˲⁼⁻¹ | coe-dom t˲⁼ via (Γ,Γ⁼) |
  ||| coe-codom t˲⁼ via (Γ,Γ⁼) | t˲⁼,t⁼ | t˲⁼∘σ via Γ of t˲=t˲ | t˲⁼·t˲⁼ via t˲
  export
  elaborateSubNormEq : Low.Sig -> Low.Ctx -> Low.Ctx -> Low.SubNorm -> Low.SubNorm -> SubNormEq -> Either ElabError ()
  elaborateSubNormEq sig dom cod s0 s1 SubNormEq.Terminal =
    if cod == [<] && s0 == [<] && s1 == [<]
      then Right ()
      else Left (CtxMismatch [<] cod)
  elaborateSubNormEq sig dom cod s0 s1 SubNormEq.Refl =
    if s0 == s1 then Right () else Left (SubNormMismatch s0 s1)
  elaborateSubNormEq sig dom cod s0 s1 (SubNormEq.Sym seq) =
    elaborateSubNormEq sig dom cod s1 s0 seq
  elaborateSubNormEq sig dom cod s0 s1 (SubNormEq.CoeDom seq g geq) = do
    lowG <- elaborateCtx sig g
    _ <- elaborateSubNormEq sig lowG cod s0 s1 seq
    elaborateCtxEq sig lowG dom geq
  elaborateSubNormEq sig dom cod s0 s1 (SubNormEq.CoeCodom seq g geq) = do
    lowG <- elaborateCtx sig g
    _ <- elaborateSubNormEq sig dom lowG s0 s1 seq
    elaborateCtxEq sig lowG cod geq
  elaborateSubNormEq sig dom cod s0 s1 (SubNormEq.Ext seq eeq) =
    case (cod, s0, s1) of
      (delta :< ty, s0' :< t0, s1' :< t1) => do
        _ <- elaborateSubNormEq sig dom delta s0' s1' seq
        elaborateElemEq sig dom (substTy ty (embed s1')) t0 t1 eeq
      _ => Left (NotACtxExtension cod)
  elaborateSubNormEq sig dom cod s0 s1 (SubNormEq.Chain seq e0 e1 t midG) = do
    lowMidG <- elaborateCtx sig midG
    lowE0 <- elaborateSubNorm sig lowMidG cod e0
    lowE1 <- elaborateSubNorm sig lowMidG cod e1
    _ <- elaborateSubNormEq sig lowMidG cod lowE0 lowE1 seq
    lowT <- elaborateSub sig dom lowMidG t
    let expected0 = substSubNorm lowE0 lowT
        expected1 = substSubNorm lowE1 lowT
    if expected0 == s0 && expected1 == s1
      then Right ()
      else Left (SubNormMismatch expected0 s0)
  elaborateSubNormEq sig dom cod s0 s1 (SubNormEq.Trans seq0 seq1 midS) = do
    lowMid <- elaborateSubNorm sig dom cod midS
    _ <- elaborateSubNormEq sig dom cod s0 lowMid seq0
    elaborateSubNormEq sig dom cod lowMid s1 seq1

  ||| Given a well-formed Sig, and both Ctx's it relates —
  ||| Γ⁼ ::= ε | refl | Γ⁼⁻¹ | Γ⁼ ᐅ T⁼ | Γ⁼ · Γ⁼ via Γ
  export
  elaborateCtxEq : Low.Sig -> Low.Ctx -> Low.Ctx -> CtxEq -> Either ElabError ()
  elaborateCtxEq sig g0 g1 CtxEq.Empty =
    case (g0, g1) of
      ([<], [<]) => Right ()
      _          => Left (CtxMismatch g0 g1)
  elaborateCtxEq sig g0 g1 CtxEq.Refl =
    if g0 == g1
      then Right ()
      else Left (CtxMismatch g0 g1)
  elaborateCtxEq sig g0 g1 (CtxEq.Sym geq) =
    elaborateCtxEq sig g1 g0 geq
  elaborateCtxEq sig g0 g1 (CtxEq.Ext geq aeq) =
    case (g0, g1) of
      (g0' :< a0, g1' :< a1) => do
        _ <- elaborateCtxEq sig g0' g1' geq
        elaborateTyEq sig g0' a0 a1 aeq
      _ => Left (NotACtxExtension g0)
  elaborateCtxEq sig g0 g1 (CtxEq.Trans geq0 geq1 midG) = do
    lowMidG <- elaborateCtx sig midG
    _ <- elaborateCtxEq sig g0 lowMidG geq0
    elaborateCtxEq sig lowMidG g1 geq1

  ||| Given a well-formed Sig and Ctx, and both Ty's it relates.
  export
  elaborateTyEq : Low.Sig -> Low.Ctx -> Low.Ty.Ty -> Low.Ty.Ty -> TyEq -> Either ElabError ()
  elaborateTyEq sig ctx t0 t1 TyEq.ZeroTy =
    if t0 == Low.Ty.ZeroTy && t1 == Low.Ty.ZeroTy then Right () else Left (TyMismatch t0 t1)
  elaborateTyEq sig ctx t0 t1 TyEq.OneTy =
    if t0 == Low.Ty.OneTy && t1 == Low.Ty.OneTy then Right () else Left (TyMismatch t0 t1)
  elaborateTyEq sig ctx t0 t1 TyEq.NatTy =
    if t0 == Low.Ty.NatTy && t1 == Low.Ty.NatTy then Right () else Left (TyMismatch t0 t1)
  elaborateTyEq sig ctx t0 t1 TyEq.UniverseTy =
    if t0 == Low.Ty.UniverseTy && t1 == Low.Ty.UniverseTy then Right () else Left (TyMismatch t0 t1)
  elaborateTyEq sig ctx t0 t1 TyEq.Refl =
    if t0 == t1 then Right () else Left (TyMismatch t0 t1)
  elaborateTyEq sig ctx t0 t1 (TyEq.Sym teq) =
    elaborateTyEq sig ctx t1 t0 teq
  elaborateTyEq sig ctx t0 t1 (TyEq.Subst g teq a0 a1 s) = do
    lowG <- elaborateCtx sig g
    lowA0 <- elaborateTy sig lowG a0
    lowA1 <- elaborateTy sig lowG a1
    lowS <- elaborateSub sig ctx lowG s
    _ <- elaborateTyEq sig lowG lowA0 lowA1 teq
    let expected0 = substTy lowA0 lowS
        expected1 = substTy lowA1 lowS
    if expected0 == t0 && expected1 == t1
      then Right ()
      else Left (TyMismatch expected0 t0)
  elaborateTyEq sig ctx t0 t1 (TyEq.El eeq) =
    case (t0, t1) of
      (Low.Ty.El e0, Low.Ty.El e1) => elaborateElemEq sig ctx Low.Ty.UniverseTy e0 e1 eeq
      _                            => Left (UnexpectedTyShape "El _" t0)
  elaborateTyEq sig ctx t0 t1 (TyEq.CoeCtx teq g geq) = do
    lowG <- elaborateCtx sig g
    _ <- elaborateTyEq sig lowG t0 t1 teq
    elaborateCtxEq sig lowG ctx geq
  elaborateTyEq sig ctx t0 t1 (TyEq.ZeroElim t) = do
    _ <- elaborateElem sig ctx Low.Ty.ZeroTy t
    Right ()
  elaborateTyEq sig ctx t0 t1 (TyEq.PiTy aEq bEq) =
    case (t0, t1) of
      (Low.Ty.PiTy a0 b0, Low.Ty.PiTy a1 b1) => do
        _ <- elaborateTyEq sig ctx a0 a1 aEq
        elaborateTyEq sig (ctx :< a1) b0 b1 bEq
      _ => Left (UnexpectedTyShape "_ → _" t0)
  elaborateTyEq sig ctx t0 t1 (TyEq.SigmaTy aEq bEq) =
    case (t0, t1) of
      (Low.Ty.SigmaTy a0 b0, Low.Ty.SigmaTy a1 b1) => do
        _ <- elaborateTyEq sig ctx a0 a1 aEq
        elaborateTyEq sig (ctx :< a1) b0 b1 bEq
      _ => Left (UnexpectedTyShape "_ ⨯ _" t0)
  elaborateTyEq sig ctx t0 t1 (TyEq.Quotient aEq rEq) =
    case (t0, t1) of
      (Low.Ty.Quotient a0 r0, Low.Ty.Quotient a1 r1) => do
        _ <- elaborateTyEq sig ctx a0 a1 aEq
        elaborateTyEq sig (ctx :< a1 :< substTy a1 Wk) r0 r1 rEq
      _ => Left (UnexpectedTyShape "_ / _" t0)
  elaborateTyEq sig ctx t0 t1 (TyEq.EqTy aEq bEq tEq) =
    case (t0, t1) of
      (Low.Ty.EqTy a0 b0 ty0, Low.Ty.EqTy a1 b1 ty1) => do
        _ <- elaborateTyEq sig ctx ty0 ty1 tEq
        _ <- elaborateElemEq sig ctx ty1 a0 a1 aEq
        elaborateElemEq sig ctx ty1 b0 b1 bEq
      _ => Left (UnexpectedTyShape "_ ≡ _ ∈ _" t0)
  elaborateTyEq sig ctx t0 t1 (TyEq.Trans teq0 teq1 midTy) = do
    lowMid <- elaborateTy sig ctx midTy
    _ <- elaborateTyEq sig ctx t0 lowMid teq0
    elaborateTyEq sig ctx lowMid t1 teq1

||| Given the Σ elaborated so far, checks one more entry Γ ⊦ x ≔ a : A
||| against it (including x ∉ Σ) and returns the low-level entry to snoc on.
export
elaborateSigEntry : Low.Sig -> Surface.SigEntry -> Either ElabError Low.SigEntry
elaborateSigEntry sig (MkSigEntry g x a t) = do
  lowG <- elaborateCtx sig g
  lowT <- elaborateTy sig lowG t
  lowA <- elaborateElem sig lowG lowT a
  case sigLookup x sig of
    Just _  => Left (SigIdentifierAlreadyDefined x)
    Nothing => Right (lowG, x, lowA, lowT)

||| Σ ::= ε | Σ (Γ ⊦ x ≔ a : A)  (assumes nothing — this is the root judgement)
export
elaborateSig : Surface.Sig -> Either ElabError Low.Sig
elaborateSig [<] = Right [<]
elaborateSig (rest :< entry) = do
  lowRest <- elaborateSig rest
  lowEntry <- elaborateSigEntry lowRest entry
  Right (lowRest :< lowEntry)
