module Nova.Surface.Elaboration.Implementation.Tactic.Trivial

import Me.Russoul.Data.Location

import Data.SnocList

import Nova.Core.Context
import Nova.Core.Language
import Nova.Core.Monad
import Nova.Core.Evaluation
import Nova.Core.Conversion

import Nova.Surface.Language

-- This module contains support code for the "trivial" tactic

applyTrivialNu : Signature -> Omega -> Typ -> M (Maybe Elem)
applyTrivialNu sig omega (TyEqTy a b) = MMaybe.do
  case !(liftM $ conv sig omega a b) of
    True => MMaybe.do
      return (TyEqVal a)
    False => nothing
applyTrivialNu sig omega (ElEqTy a b ty) = MMaybe.do
  case !(liftM $ conv sig omega a b) of
    True => MMaybe.do
      return (ElEqVal ty a)
    False => nothing
applyTrivialNu sig omega _ = nothing

public export
applyTrivial : Signature -> Omega -> Typ -> M (Maybe Elem)
applyTrivial sig omega ty = applyTrivialNu sig omega !(liftM $ openEval sig omega ty)
