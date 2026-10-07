module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.DualNumber
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Exercise 111.35.4 -/
@[stacks 029G] #check (DualNumberPair.spec_isPushout :
  ∀ (K : Type u) [Field K],
    CategoryTheory.IsPushout (DualNumberPair.fromClosedPoint K)
      (DualNumberPair.fromClosedPoint K) (DualNumberPair.inl K)
      (DualNumberPair.inr K))
