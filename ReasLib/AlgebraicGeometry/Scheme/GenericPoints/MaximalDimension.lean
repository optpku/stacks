/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Dimension
public import ReasLib.Topology.Specialization.Dimension

@[expose] public section

open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The irreducible components whose generic points have greatest value under the dimension
function `δ`. -/
noncomputable def maximalDimensionComponents (X : Scheme.{u}) (δ : X → ℤ)
    [IsDimensionFunction δ] : Set (irreducibleComponents X) :=
  {Z | ∀ W : irreducibleComponents X,
    δ (genericPoints.ofComponent W).1 ≤ δ (genericPoints.ofComponent Z).1}

/-- Membership in `maximalDimensionComponents X δ` means having greatest generic-point
`δ`-value among all irreducible components. -/
theorem mem_maximalDimensionComponents_iff (X : Scheme.{u}) (δ : X → ℤ)
    [IsDimensionFunction δ] (Z : irreducibleComponents X) :
    Z ∈ maximalDimensionComponents X δ ↔
      ∀ W : irreducibleComponents X,
        δ (genericPoints.ofComponent W).1 ≤ δ (genericPoints.ofComponent Z).1 := sorry

/-- The union of the irreducible components with greatest generic-point value under `δ`. -/
noncomputable def maximalDimensionComponentSupport (X : Scheme.{u}) (δ : X → ℤ)
    [IsDimensionFunction δ] : Set X :=
  ⋃ Z ∈ maximalDimensionComponents X δ, (Z : Set X)

/-- A point lies in `maximalDimensionComponentSupport X δ` exactly when it lies in a
maximal-dimension irreducible component. -/
theorem mem_maximalDimensionComponentSupport_iff (X : Scheme.{u}) (δ : X → ℤ) [IsDimensionFunction δ]
    (x : X) :
    x ∈ maximalDimensionComponentSupport X δ ↔
      ∃ Z : irreducibleComponents X,
        Z ∈ maximalDimensionComponents X δ ∧ x ∈ (Z : Set X) := sorry

end AlgebraicGeometry.Scheme
