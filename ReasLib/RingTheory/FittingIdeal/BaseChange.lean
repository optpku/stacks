/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FittingIdeal.Basic

/-!
# Base change of Fitting ideals

This file records the intrinsic base-change theorem for Fitting ideals.  Its statement uses the
canonical tensor-product model for extension of scalars and requires no flatness or presentation
choice.
@stack 07ZA
-/

@[expose] public section

universe u v w

open scoped FittingIdeal TensorProduct

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Fitting ideals commute with extension of scalars. -/
@[stacks 07ZA "Fitting ideals commute with base change"]
theorem fittingIdeal_baseChange
    {R' : Type w} [CommRing R'] [Algebra R R'] (k : ℕ) :
    Fit[R']_(k)(R' ⊗[R] M) =
      Ideal.map (algebraMap R R') (Fit[R]_(k)(M)) := sorry

end
