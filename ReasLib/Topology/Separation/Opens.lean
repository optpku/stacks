/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sets.Opens

@[expose] public section

universe u

namespace TopologicalSpace

/-- A topological space is T₀ if and only if every pair of distinct points has an open set
containing exactly one of the two points. -/
theorem t0Space_iff_exists_opens (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Pairwise (fun x y : X => ∃ U : Opens X, Xor (x ∈ U) (y ∈ U)) := sorry

/-- A topological space is Hausdorff if and only if every pair of distinct points belongs
respectively to two disjoint open sets. -/
theorem t2Space_iff_exists_opens (X : Type u) [TopologicalSpace X] :
    T2Space X ↔ Pairwise (fun x y : X => ∃ U V : Opens X, x ∈ U ∧ y ∈ V ∧ Disjoint U V) := sorry

end TopologicalSpace
