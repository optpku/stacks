/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Irreducible

@[expose] public section

universe u

namespace Topology

/-- A topological space is irreducible exactly when it is nonempty and every covering by two
closed subsets has one member equal to the whole space. -/
theorem irreducibleSpace_iff_nonempty_closed_union (space : Type u) [TopologicalSpace space] :
    IrreducibleSpace space ↔
      Nonempty space ∧
        (∀ firstClosed secondClosed : Set space,
          IsClosed firstClosed →
            IsClosed secondClosed →
              firstClosed ∪ secondClosed = Set.univ →
                firstClosed = Set.univ ∨ secondClosed = Set.univ) := by
  sorry

end Topology
