/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Connected.Clopen

/-!
# Underlying sets of connected components

Mathlib models `ConnectedComponents X` as a quotient of points.  This leaf supplies the canonical
representative-independent subset associated to a quotient component.
-/

@[expose] public section

universe u

open Set

variable {X : Type u} [TopologicalSpace X]

namespace ConnectedComponents

/-- The subset of `X` represented by a connected-component quotient class. -/
def set (C : ConnectedComponents X) : Set X :=
  Quotient.liftOn C connectedComponent (fun _ _ hxy ↦ hxy)

/-- The set associated to the component of a point is its usual connected component. -/
theorem set_coe (x : X) : set (x : ConnectedComponents X) = connectedComponent x := by
  rfl

/-- Membership in the set represented by `C` means that the point belongs to that quotient
component. -/
theorem mem_set_iff_coe_eq {C : ConnectedComponents X} {x : X} :
    x ∈ C.set ↔ (x : ConnectedComponents X) = C := by
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [set_coe]
  exact ConnectedComponents.coe_eq_coe'.symm

end ConnectedComponents
