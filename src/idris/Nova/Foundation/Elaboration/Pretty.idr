module Nova.Foundation.Elaboration.Pretty

import Nova.Foundation.Syntax
import Nova.Foundation.Pretty
import Nova.Foundation.Elaboration.Elaborator

%default covering

export
prettyElabError : ElabError -> String
prettyElabError (NotYetSupported msg) =
  "not yet supported: " ++ msg
prettyElabError (CtxMismatch g0 g1) =
  "context mismatch: " ++ prettyCtx g0 ++ " ≠ " ++ prettyCtx g1
prettyElabError (NotACtxExtension g) =
  "expected a non-empty context (Γ ᐅ A), got: " ++ prettyCtx g
prettyElabError (TyMismatch t0 t1) =
  "type mismatch: " ++ prettyTy t0 ++ " ≠ " ++ prettyTy t1
prettyElabError (ElemMismatch e0 e1) =
  "element mismatch: " ++ prettyElem e0 ++ " ≠ " ++ prettyElem e1
prettyElabError (UnexpectedTyShape desc t) =
  "expected a type of the form " ++ desc ++ ", got: " ++ prettyTy t
prettyElabError (CtxVarOutOfBounds g n) =
  "index out of bounds: " ++ prettyElemAtom (CtxVar n) ++ " in " ++ prettyCtx g
prettyElabError (SigIdentifierNotFound x) =
  "identifier not found in signature: " ++ x
prettyElabError (UnexpectedElemShape desc e) =
  "expected an element of the form " ++ desc ++ ", got: " ++ prettyElem e
prettyElabError (SubNormMismatch s0 s1) =
  "substitution mismatch: " ++ prettySubNorm s0 ++ " ≠ " ++ prettySubNorm s1
prettyElabError (SigIdentifierAlreadyDefined x) =
  "identifier already defined in signature: " ++ x
