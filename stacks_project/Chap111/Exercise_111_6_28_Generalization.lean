module

public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Connected.Basic
public import ReasLib.Topology.ConnectedComponents.Basic

/-!
# Generalization-stability of connected components

Connected components are closed, hence stable under specialization. The dual fact, stability
under generalization, is not in mathlib; it follows from maximality of `connectedComponent`
together with connectedness of closures of points.
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
