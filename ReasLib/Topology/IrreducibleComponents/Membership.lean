/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Irreducible

@[expose] public section

namespace TopologicalSpace

/-- A subset belongs to the irreducible components exactly when it is a maximal irreducible subset. -/
theorem mem_irreducibleComponents_iff {X : Type u} [TopologicalSpace X] (s : Set X) :
    s ∈ irreducibleComponents X ↔ Maximal IsIrreducible s := sorry

end TopologicalSpace
