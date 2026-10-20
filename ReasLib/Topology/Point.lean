/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace

@[expose] public section

universe u

namespace Topology

/-- A point belongs to the set of closed points exactly when the closure of its
singleton is that singleton. -/
theorem mem_closedPoints_iff_closure_eq {X : Type u} [TopologicalSpace X]
    (x : X) : x ∈ closedPoints X ↔ closure ({x} : Set X) = {x} := sorry

end Topology
