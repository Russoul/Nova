module Nova.Surface.Elaboration.Pretty

import Me.Russoul.Data.Location

import Nova.Control.Monad.Id
import Nova.Control.Monad.Reader

import Data.AVL
import Data.Fin
import Data.SnocList
import Data.String

import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Text.PrettyPrint.Prettyprinter

import Nova.Core.Language
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
  pretty : Signature -> Omega -> ElaborationEntry -> PrettyM (Doc Ann)
  pretty sig omega (ElemElaboration ctx tm p ty) = Reader.do
    pure $
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
  pretty sig omega (TypeElaboration ctx tm p) = Reader.do
    pure $
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
  pretty sig omega (ElemElimElaboration ctx head headTy tm p ty) = Reader.do
    pure $
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

  public export
  prettyDefault : Signature -> Omega -> ElaborationEntry -> Doc Ann
  prettyDefault sig omega entry = pretty sig omega entry prettyCfgDefault

namespace TopLevelError
  public export
  pretty : Signature -> TopLevelError -> PrettyM (Doc Ann)
  pretty sig (Stuck omega stuckElab stuckCons) = Reader.do
    let unsolvedMetas = filter (\(_, x) => isMetaType x || isMetaElem x) (List.inorder omega)
    pure $
      pretty "----------- Stuck unification constraints (#\{show (length stuckCons)}): -------------"
       <+>
      hardline
       <+>
      vsep !(List.for stuckCons $ \(con, str) => Reader.do
             pure $
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
      vsep !(List.for stuckElab $ \(elab, err) => Reader.do
        pure $
          !(pretty sig omega elab)
           <+>
          hardline
           <+>
          pretty "Reason: \{err}")
  pretty sig (UnificationError omega (con, err)) = Reader.do
    pure $
      "----------- Disunifier found: -------------"
       <+>
      hardline
       <+>
      !(prettyConstraintEntry sig omega con)
       <+>
      hardline
       <+>
      pretty "Reason: \{err}"
  pretty sig (ElaborationError omega (elab, err)) = Reader.do
    pure $
       "----------- Elaborator failed: -------------"
        <+>
       hardline
        <+>
       pretty (show elab)
        <+>
       hardline
        <+>
       pretty "Reason: \{err}"

  public export
  prettyDefault : Signature -> TopLevelError -> Doc Ann
  prettyDefault sig err = pretty sig err prettyCfgDefault

namespace Elaboration
  public export
  prettyResult : Signature -> Elaboration.Result -> PrettyM (Doc Ann)
  prettyResult sig (Success omega new) = Reader.do
    pure $
      "Success, sub-problems:"
       <+>
      hardline
       <+>
      vsep !(List.for new (pretty sig omega))
  prettyResult sig (Stuck reason) = Reader.do
    pure (pretty "Stuck, reason: \{reason}")
  prettyResult sig (Error reason) = Reader.do
    pure (pretty "Error, reason: \{reason}")

  public export
  prettyResultDefault : Signature -> Elaboration.Result -> Doc Ann
  prettyResultDefault sig r = prettyResult sig r prettyCfgDefault
