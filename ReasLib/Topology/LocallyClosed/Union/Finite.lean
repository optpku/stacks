module

public import ReasLib.Topology.LocallyClosed.FiniteUnion
public import ReasLib.Topology.LocallyClosed.Union.Basic

/-!
# Finite-to-Arbitrary Locally Closed Unions

This leaf provides the one-way bridge from finite locally closed
decompositions to the arbitrary geometric predicate.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

/-- A finite union of locally closed subsets is an arbitrary union of locally
closed subsets after forgetting finiteness. -/
theorem IsFiniteUnionOfLocallyClosed.isUnionOfLocallyClosed {T : Set X}
    (hT : IsFiniteUnionOfLocallyClosed T) : IsUnionOfLocallyClosed T := by
  rcases hT with ⟨S, _, hS, rfl⟩
  exact ⟨S, hS, rfl⟩
