/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.Topology.Sets.Closeds

@[expose] public section

open Set Topology TopologicalSpace

universe u v

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Type u} [TopologicalSpace X] {R : Type v} [Zero R]

/-- The geometric support of a locally supported function is the union of the closures of the points
where its coefficient is nonzero. -/
def geometricSupport (α : Function.locallyFinsupp X R) : Set X :=
  ⋃ x ∈ Function.support α, closure {x}

/-- The geometric support is the union of the point closures indexed by coefficient support. -/
theorem geometricSupport_def (α : Function.locallyFinsupp X R) :
    geometricSupport α = ⋃ x ∈ Function.support α, closure {x} := sorry

/-- A point belongs to the geometric support exactly when it specializes from a point with
nonzero coefficient. -/
theorem mem_geometricSupport (α : Function.locallyFinsupp X R) (y : X) :
    y ∈ geometricSupport α ↔ ∃ x : X, α x ≠ 0 ∧ y ∈ closure {x} := sorry

/-- The geometric support of a locally supported function is closed. -/
theorem isClosed_geometricSupport (α : Function.locallyFinsupp X R) :
    IsClosed (geometricSupport α) := sorry

/-- Containment of the geometric support in a closed set is equivalent to containment of
the coefficient support in that closed set. -/
theorem geometricSupport_subset_closed_iff (α : Function.locallyFinsupp X R)
    (T : Closeds X) :
    geometricSupport α ⊆ T.carrier ↔ α.support ⊆ T.carrier := sorry

end AlgebraicGeometry.AlgebraicCycle
