module Nova.Foundation.Elaboration.Elaborator

-- Elaborates the proof-term surface syntax (Nova.Foundation.Elaboration.Syntax)
-- directly into the checked, low-level object language
-- (Nova.Foundation.Syntax) — bypassing Nova.Foundation.Derivation's
-- TypingRule/Truth/generate machinery entirely.
--
-- Every elaborateX is in *check* mode: it is given its "indices" as already
-- well-formed low-level values, and only has to verify/build the value
-- itself, never infer an index:
--   elaborateCtx     : assumes nothing
--   elaborateCtxEq   : given both Ctx's it is supposed to relate
--   elaborateTy      : given a well-formed Ctx
--   elaborateTyEq    : given a well-formed Ctx and both Ty's
--   elaborateSub     : given the domain and codomain Ctx's
--   elaborateSubNorm : given the domain and codomain Ctx's
--   elaborateElem    : given a well-formed Ctx and the Ty checked against
--   elaborateElemEq  : given a well-formed Ctx, the Ty, and both Elem's
-- Equality checks throughout are syntactic (`==`), never up-to-computation.
--
-- Ctx and Ty are implemented below; Elem/Sub/SubNorm/CtxEq/TyEq/ElemEq/
-- SubNormEq are forward-declared (same mutual block, correct types) but
-- stubbed with NotYetSupported until their own implementation pass.

import Data.SnocList
import Nova.Foundation.Subst
import Nova.Foundation.Syntax as Low
import Nova.Foundation.Elaboration.Syntax as Surface

%default covering

public export
data ElabError : Type where
  ||| Placeholder for elaborator pieces not implemented yet.
  NotYetSupported : String -> ElabError

mutual
  ||| Γ ::= ε | Γ ᐅ T  (assumes nothing)
  export
  elaborateCtx : Surface.Ctx.Ctx -> Either ElabError Low.Ctx
  elaborateCtx Surface.Ctx.Empty = Right [<]
  elaborateCtx (Surface.Ctx.Ext g a) = do
    lowG <- elaborateCtx g
    lowA <- elaborateTy lowG a
    Right (lowG :< lowA)

  ||| Given a well-formed Ctx, checks a surface Ty relative to it.
  export
  elaborateTy : Low.Ctx -> Surface.Ty.Ty -> Either ElabError Low.Ty.Ty
  elaborateTy ctx Surface.Ty.ZeroTy     = Right Low.Ty.ZeroTy
  elaborateTy ctx Surface.Ty.OneTy      = Right Low.Ty.OneTy
  elaborateTy ctx Surface.Ty.NatTy      = Right Low.Ty.NatTy
  elaborateTy ctx Surface.Ty.UniverseTy = Right Low.Ty.UniverseTy
  elaborateTy ctx (Surface.Ty.PiTy a b) = do
    lowA <- elaborateTy ctx a
    lowB <- elaborateTy (ctx :< lowA) b
    Right (Low.Ty.PiTy lowA lowB)
  elaborateTy ctx (Surface.Ty.SigmaTy a b) = do
    lowA <- elaborateTy ctx a
    lowB <- elaborateTy (ctx :< lowA) b
    Right (Low.Ty.SigmaTy lowA lowB)
  elaborateTy ctx (Surface.Ty.Quotient a r) = do
    lowA <- elaborateTy ctx a
    lowR <- elaborateTy (ctx :< lowA :< substTy lowA Wk) r
    Right (Low.Ty.Quotient lowA lowR)
  elaborateTy ctx (Surface.Ty.EqTy a b t) = do
    lowT <- elaborateTy ctx t
    lowA <- elaborateElem ctx lowT a
    lowB <- elaborateElem ctx lowT b
    Right (Low.Ty.EqTy lowA lowB lowT)
  elaborateTy ctx (Surface.Ty.El e) = do
    lowE <- elaborateElem ctx Low.Ty.UniverseTy e
    Right (Low.Ty.El lowE)
  elaborateTy ctx (Surface.Ty.Subst g a s) = do
    lowG <- elaborateCtx g
    lowA <- elaborateTy lowG a
    lowS <- elaborateSub ctx lowG s
    Right (substTy lowA lowS)
  elaborateTy ctx (Surface.Ty.CoeCtx a g geq) = do
    lowG <- elaborateCtx g
    lowA <- elaborateTy lowG a
    _ <- elaborateCtxEq lowG ctx geq
    Right lowA

  ||| Given a well-formed Ctx and the Ty it's checked against — not yet
  ||| implemented, forward-declared so elaborateTy can call it.
  export
  elaborateElem : Low.Ctx -> Low.Ty.Ty -> Surface.Elem.Elem -> Either ElabError Low.Elem.Elem
  elaborateElem ctx ty e = Left (NotYetSupported "elaborateElem")

  ||| Given the domain and codomain Ctx's — not yet implemented.
  export
  elaborateSub : Low.Ctx -> Low.Ctx -> Surface.Sub.Sub -> Either ElabError Low.Sub.Sub
  elaborateSub dom cod s = Left (NotYetSupported "elaborateSub")

  ||| Given both Ctx's it relates — not yet implemented.
  export
  elaborateCtxEq : Low.Ctx -> Low.Ctx -> CtxEq -> Either ElabError ()
  elaborateCtxEq g0 g1 geq = Left (NotYetSupported "elaborateCtxEq")
