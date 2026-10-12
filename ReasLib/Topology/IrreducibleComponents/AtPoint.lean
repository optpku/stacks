/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Irreducible

/-!
# Irreducible components through a point

This file defines the set of irreducible components of a topological space
that contain a specified point.
-/

@[expose] public section

universe u

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- The irreducible components of a topological space that contain a specified point. -/
def irreducibleComponentsAt (x : X) : Set (irreducibleComponents X) :=
  {Z | x ∈ (Z : Set X)}

/-- Membership in `irreducibleComponentsAt x` means that the component contains `x`. -/
@[simp]
theorem mem_irreducibleComponentsAt {x : X} {Z : irreducibleComponents X} :
    Z ∈ irreducibleComponentsAt x ↔ x ∈ (Z : Set X) := sorry

end TopologicalSpace
