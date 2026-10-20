/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup

/-!
# Point cycles

This file defines the degree-indexed cycle supported with coefficient one at a single point.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

variable {X : Scheme.{u}}

/-- The singleton cycle at a point whose dimension is the prescribed degree. -/
theorem point_mem_dimensionSubgroup (d : X → ℤ) (k : ℤ) (x : X) (hx : d x = k) :
    @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _ x 1 ∈
      AlgebraicCycle.dimensionSubgroup d k := sorry

/-- The degree-`k` cycle with coefficient one at `x` and zero elsewhere. -/
noncomputable def point (d : X → ℤ) (k : ℤ) (x : X) (hx : d x = k) :
    CycleGroup X d k :=
  ⟨@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _ x 1,
    point_mem_dimensionSubgroup d k x hx⟩

/-- The coefficient function of a point cycle is the corresponding singleton function. -/
theorem point_apply (d : X → ℤ) (k : ℤ) (x : X) (hx : d x = k) (y : X) :
    toAlgebraicCycle d k (point d k x hx) y =
      @ite ℤ (y = x) (Classical.propDecidable _) 1 0 := sorry

end AlgebraicGeometry.CycleGroup
