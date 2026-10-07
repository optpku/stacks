module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maximal Connected Subsets

Mathlib represents connected components by the point-indexed sets
`connectedComponent x`.  This module provides the equivalent maximal-subset
view and its uniqueness API.
-/

@[expose] public section

universe u

open Set

variable {X : Type u} [TopologicalSpace X]

/-- A subset is a maximal connected subset exactly when it is the
connected component of one of its points. -/
@[stacks 004S "connected components as maximal connected subsets"]
theorem maximal_isConnected_iff_eq_connectedComponent (T : Set X) :
    Maximal IsConnected T ↔ ∃ x : X, T = connectedComponent x := sorry

namespace IsConnected

/-- A connected subset is contained in a unique maximal connected subset. -/
@[stacks 004T "connected subsets lie in unique connected components"]
theorem existsUnique_maximalSuperset {T : Set X} (hT : IsConnected T) :
    ∃! C : Set X, Maximal IsConnected C ∧ T ⊆ C := sorry

end IsConnected

/-- Every point belongs to a unique maximal connected subset. -/
@[stacks 004T "every point lies in a unique connected component"]
theorem existsUnique_maximal_isConnected_containing (x : X) :
    ∃! C : Set X, Maximal IsConnected C ∧ x ∈ C := sorry
