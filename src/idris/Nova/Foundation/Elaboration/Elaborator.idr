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
-- Ctx, Ty, Sub, CtxEq, TyEq, and Elem are implemented below (including
-- Elem.Var, signature variables, now that Sig is threaded through);
-- SubNorm/ElemEq/SubNormEq are forward-declared (same mutual block, correct
-- types) but stubbed with NotYetSupported until their own implementation pass.

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
  elaborateElem sig ctx ty (Elem.EqTyCode a a0 a1) =
    if ty == Low.Ty.UniverseTy
      then do
        lowA <- elaborateElem sig ctx Low.Ty.UniverseTy a
        lowA0 <- elaborateElem sig ctx (Low.Ty.El lowA) a0
        lowA1 <- elaborateElem sig ctx (Low.Ty.El lowA) a1
        Right (Low.Elem.EqTy lowA0 lowA1 lowA)
      else Left (TyMismatch Low.Ty.UniverseTy ty)
  elaborateElem sig ctx ty (Elem.SigmaIntro a b) =
    case ty of
      Low.Ty.SigmaTy bigA bigB => do
        lowA <- elaborateElem sig ctx bigA a
        lowB <- elaborateElem sig ctx (substTy bigB (Ext Id lowA)) b
        Right (Low.Elem.SigmaIntro lowA lowB)
      _ => Left (UnexpectedTyShape "_ ⨯ _" ty)

  ||| Given a well-formed Sig and Ctx, the Ty, and both Elem's it relates —
  ||| not yet implemented, forward-declared so elaborateElem can call it.
  export
  elaborateElemEq : Low.Sig -> Low.Ctx -> Low.Ty.Ty -> Low.Elem.Elem -> Low.Elem.Elem -> ElemEq -> Either ElabError ()
  elaborateElemEq sig ctx ty e0 e1 eeq = Left (NotYetSupported "elaborateElemEq")

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

  ||| Given a well-formed Sig, and the domain and codomain Ctx's — not yet
  ||| implemented, forward-declared so elaborateElem's Var case can call it.
  export
  elaborateSubNorm : Low.Sig -> Low.Ctx -> Low.Ctx -> Surface.SubNorm.SubNorm -> Either ElabError Low.SubNorm
  elaborateSubNorm sig dom cod s = Left (NotYetSupported "elaborateSubNorm")

  ||| Given a well-formed Sig, the domain/codomain Ctx's, and both SubNorm's
  ||| it relates — not yet implemented.
  export
  elaborateSubNormEq : Low.Sig -> Low.Ctx -> Low.Ctx -> Low.SubNorm -> Low.SubNorm -> SubNormEq -> Either ElabError ()
  elaborateSubNormEq sig dom cod s0 s1 seq = Left (NotYetSupported "elaborateSubNormEq")

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
