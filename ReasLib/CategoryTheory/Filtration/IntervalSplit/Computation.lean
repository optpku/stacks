/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.IntervalSplit.Basic

/-!
# Computations for Interval-Split Filtered Objects

This module records the arrow and factorization formulas for the interval-tail filtration.  These
are the stable downstream interface for constructing filtered maps into interval-split objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  [HasFiniteBiproducts C]
variable (a b : ℤ) (J : Set.Icc a b → C)

namespace IntervalTail.Subobject

/-- A map into an interval biproduct factors through the `p`-tail exactly when its components at
all excluded indices vanish. -/
theorem factors_iff_component_zero {p : ℤ} {W : C} (g : W ⟶ ⨁ J) :
    (IntervalTail.subobject a b J p).Factors g ↔
      ∀ i : Set.Icc a b, ¬ p ≤ i.1 → g ≫ biproduct.π J i = 0 := sorry

end IntervalTail.Subobject

namespace IntervalSplit.Stage

/-- The `p`-th stage arrow has zero component at every interval summand strictly below `p`. -/
theorem arrow_comp_π_eq_zero_of_not_le (p : ℤ) (i : Set.Icc a b) (hi : ¬ p ≤ i.1) :
    ((IntervalSplit.filteredObject a b J).obj.filtration.stage p).arrow ≫
      biproduct.π J i = 0 := sorry

end IntervalSplit.Stage

end CategoryTheory.FilteredObject
