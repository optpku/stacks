/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Relative complements of closed subsets

The complement of a relatively closed subset in an open set is open in the ambient space.
-/

@[expose] public section

open TopologicalSpace

namespace TopologicalSpace.Opens

/-- The complement of a subset closed in `U`, regarded as an open of the ambient space. -/
def relativeComplement {X : Type*} [TopologicalSpace X] (U : Opens X) (Z : Set X)
    (hclosed : IsClosed ((Subtype.val : U → X) ⁻¹' Z)) : Opens X :=
  ⟨(U : Set X) \ Z, sorry⟩

/-- A relative complement is contained in its ambient open. -/
theorem relativeComplement_le {X : Type*} [TopologicalSpace X]
    (U : Opens X) (Z : Set X) (hclosed : IsClosed ((Subtype.val : U → X) ⁻¹' Z)) :
    relativeComplement U Z hclosed ≤ U := by
  intro x hx
  exact hx.1

/-- The carrier of a relative complement is the set difference `U \ Z`. -/
theorem relativeComplement_coe {X : Type*} [TopologicalSpace X]
    (U : Opens X) (Z : Set X) (hclosed : IsClosed ((Subtype.val : U → X) ⁻¹' Z)) :
    (relativeComplement U Z hclosed : Set X) = (U : Set X) \ Z := rfl

/-- Membership in a relative complement is membership in `U` and nonmembership in `Z`. -/
theorem mem_relativeComplement {X : Type*} [TopologicalSpace X]
    (U : Opens X) (Z : Set X) (hclosed : IsClosed ((Subtype.val : U → X) ⁻¹' Z)) (x : X) :
    x ∈ relativeComplement U Z hclosed ↔ x ∈ U ∧ x ∉ Z := Iff.rfl

end TopologicalSpace.Opens

end
