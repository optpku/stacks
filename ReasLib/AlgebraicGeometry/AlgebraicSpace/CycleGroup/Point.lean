/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic

/-! # Singleton cycles on algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The cycle with coefficient one at a point and zero at every other point. -/
noncomputable def pointCycle {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    Function.locallyFinsupp (Points X) ℤ :=
  @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _ x 1

/-- The singleton cycle of a point of relative degree `k + 1` has that degree. -/
theorem pointCycle_mem {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFiniteType f] (δ : Points B → ℤ) (k : ℤ)
    (x : Points X) (hx : relativeDimensionFunction f δ x = k + 1) :
    pointCycle x ∈ cycleGroup f δ (k + 1) := by
  classical
  intro y hy
  by_cases h : y = x
  · simpa only [h] using hx
  · simp [pointCycle, Function.locallyFinsuppWithin.single_apply, h] at hy

end AlgebraicGeometry.AlgebraicSpace.Hom
