module Nova.Surface.Elaboration.Implementation.Tactic.Trivial

import Me.Russoul.Data.Location

import Nova.Control.Monad.Id

import Data.SnocList

import Nova.Core.Context
import Nova.Core.Language
import Nova.Core.Evaluation
import Nova.Core.Conversion

import Nova.Surface.Language

-- This module contains support code for the "trivial" tactic

applyTrivialNu : Signature -> Omega -> Typ -> Maybe Elem
applyTrivialNu sig omega (TyEqTy a b) = Prelude.do
  case conv sig omega a b of
    True => Prelude.do
      pure (TyEqVal a)
    False => Nothing
applyTrivialNu sig omega (ElEqTy a b ty) = Prelude.do
  case (conv sig omega a b) of
    True => Prelude.do
      pure (ElEqVal ty a)
    False => Nothing
applyTrivialNu sig omega _ = Nothing

public export
applyTrivial : Signature -> Omega -> Typ -> Maybe Elem
applyTrivial sig omega ty = applyTrivialNu sig omega (openEval sig omega ty)
