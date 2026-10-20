module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed and Compact Subsets

The compact Hausdorff equivalence between closedness and compactness of a
subset.
-/

@[expose] public section

universe u

open Set

variable {X : Type u} [TopologicalSpace X]

namespace CompactSpace

/-- Lemma 5.12.5: in a compact Hausdorff space, a subset is closed if and only if it is compact. -/
@[stacks 08YC "closed subsets and compact subsets of compact Hausdorff spaces"]
theorem isClosed_iff_isCompact [CompactSpace X] [T2Space X] (s : Set X) :
    IsClosed s ↔ IsCompact s := by
  exact ⟨IsClosed.isCompact, IsCompact.isClosed⟩

end CompactSpace
