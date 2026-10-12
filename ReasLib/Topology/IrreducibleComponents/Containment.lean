/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Irreducible

@[expose] public section

namespace TopologicalSpace

/-- Every irreducible subset of a topological space is contained in an irreducible component. -/
theorem exists_mem_irreducibleComponents_subset_of_isIrreducible
    {X : Type*} [TopologicalSpace X] (s : Set X) (h : IsIrreducible s) :
    ∃ u ∈ irreducibleComponents X, s ⊆ u := sorry

end TopologicalSpace
