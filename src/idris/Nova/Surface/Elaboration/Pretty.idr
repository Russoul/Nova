module Nova.Surface.Elaboration.Pretty

import Me.Russoul.Data.Location

import Data.AVL
import Data.Fin
import Data.SnocList
import Data.String

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Name
import Nova.Core.Pretty
import Nova.Core.Unification

import Nova.Surface.Language
import Nova.Surface.Operator
import Nova.Surface.SemanticToken

import Nova.Surface.Elaboration.Interface


partial
public export
Show ElaborationEntry where
  show (ElemElaboration ctx tm p ty) = "... ⊦ ⟦\{show tm}⟧ ⇝ ... : ..."
  show (TypeElaboration ctx tm p) = "... ⊦ ⟦\{show tm}⟧ ⇝ ... type"
  show (ElemElimElaboration ctx head headTy tm meta ty) = "... ⊦ (... : ...) ⟦\{show tm}⟧ ⇝ ... : ..."

namespace ElaborationEntry
  public export
  pretty : Signature -> Omega -> ElaborationEntry -> M (Doc Ann)
  pretty sig omega (ElemElaboration ctx tm p ty) = M.do
    return $
      !(prettyContext sig omega ctx)
      <++>
      "⊦"
      <++>
      "⟦"
      <+>
      pretty (show tm)
      <+>
      "⟧"
      <++>
      "⇝"
      <++>
      pretty p
      <++>
      ":"
      <++>
      !(prettyTyp sig omega (map fst ctx) ty 0)
  pretty sig omega (TypeElaboration ctx tm p) = M.do
    return $
      !(prettyContext sig omega ctx)
      <++>
      "⊦"
      <++>
      "⟦"
      <+>
      pretty (show tm)
      <+>
      "⟧"
      <++>
      "⇝"
      <++>
      pretty p
      <++>
      "type"
  pretty sig omega (ElemElimElaboration ctx head headTy tm p ty) = M.do
    return $
      !(prettyContext sig omega ctx)
      <++>
      "⊦"
      <++>
      "("
      <+>
      !(prettyElem sig omega (map fst ctx) head 0)
      <++>
      ":"
      <++>
      !(prettyTyp sig omega (map fst ctx) headTy 0)
      <+>
      ")"
      <++>
      "⟦"
      <+>
      pretty (show tm)
      <+>
      "⟧"
      <++>
      "⇝"
      <++>
      pretty p
      <++>
      ":"
      <++>
      !(prettyTyp sig omega (map fst ctx) ty 0)

namespace TopLevelError
    public export
    pretty : Signature -> TopLevelError -> M (Doc Ann)
    pretty sig (Stuck omega stuckElab stuckCons) = M.do
      let unsolvedMetas = filter (\(_, x) => isMetaType x || isMetaElem x) (List.inorder omega)
      return $
        pretty "----------- Stuck unification constraints (#\{show (length stuckCons)}): -------------"
         <+>
        hardline
         <+>
        vsep !(forList stuckCons $ \(con, str) => M.do
               return $
                 !(prettyConstraintEntry sig omega con)
                  <+>
                 hardline
                  <+>
                 pretty "Reason: \{str}"
              )
         <+>
        hardline
         <+>
        pretty "----------- Unsolved meta variables (#\{show (length unsolvedMetas)}): -------------"
         <+>
        hardline
         <+>
        !(prettyOmega' sig omega unsolvedMetas)
         <+>
        hardline
         <+>
        pretty "----------- Stuck elaboration constraints (#\{show (length stuckElab)}): -------------"
         <+>
        hardline
         <+>
        vsep !(forList stuckElab $ \(elab, err) => M.do
          return $
            !(pretty sig omega elab)
             <+>
            hardline
             <+>
            pretty "Reason: \{err}")
    pretty sig (UnificationError omega (con, err)) = M.do
      return $
        "----------- Disunifier found: -------------"
         <+>
        hardline
         <+>
        !(prettyConstraintEntry sig omega con)
         <+>
        hardline
         <+>
        pretty "Reason: \{err}"
    pretty sig (ElaborationError omega (elab, err)) = M.do
      return $
         "----------- Elaborator failed: -------------"
          <+>
         hardline
          <+>
         pretty (show elab)
          <+>
         hardline
          <+>
         pretty "Reason: \{err}"



namespace Elaboration
  public export
  prettyResult : Signature -> Elaboration.Result -> M (Doc Ann)
  prettyResult sig (Success omega new) = M.do
    return $
      "Success, sub-problems:"
       <+>
      hardline
       <+>
      vsep !(forList new (pretty sig omega))
  prettyResult sig (Stuck reason) = M.do
    return (pretty "Stuck, reason: \{reason}")
  prettyResult sig (Error reason) = M.do
    return (pretty "Error, reason: \{reason}")
