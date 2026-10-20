module

public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Connected.Basic
public import ReasLib.Topology.ConnectedComponents.Basic

/-!
# Generalization-stability of connected components

Connected components and maximal connected subsets are stable under generalization.
-/

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The connected component of a point is stable under generalization. -/
theorem stableUnderGeneralization_connectedComponent (x : X) :
    StableUnderGeneralization (connectedComponent x) := sorry

/-- A maximal connected subset is stable under generalization. -/
theorem stableUnderGeneralization_of_maximal_isConnected {T : Set X} (hT : Maximal IsConnected T) :
    StableUnderGeneralization T := sorry
