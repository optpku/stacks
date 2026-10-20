/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Constructible

/-!
# Finite compact-open refinements

This module packages the finite compact-open refinements of open covers that are available in a
prespectral space.  The quasi-separated variant records the compact-intersection condition needed
by descent and Cech-style applications.
-/

@[expose] public section

universe u v

open Set TopologicalSpace Topology

namespace CompactOpens

variable {X : Type u} [TopologicalSpace X]

/-- A finite compact-open family covering a compact open and subordinate to a specified open
cover. -/
@[stacks 0069 "finite compact-open cover refinements"]
structure FiniteCoverRefinement (U : CompactOpens X) {ι : Type v} (V : ι → Opens X) where
  /-- The selected finite family of compact opens. -/
  members : Finset (CompactOpens X)
  /-- The selected family covers the original compact open. -/
  cover : (U : Set X) = ⋃ W ∈ members, (W : Set X)
  /-- Every selected compact open is contained in a member of the given cover. -/
  subordinate : ∀ W ∈ members, ∃ i, (W : Set X) ⊆ V i

namespace FiniteCoverRefinement

variable {U : CompactOpens X} {ι : Type v} {V : ι → Opens X}

/-- Build a finite compact-open cover refinement from its selected family and defining
properties. -/
def ofFinset (members : Finset (CompactOpens X))
    (cover : (U : Set X) = ⋃ W ∈ members, (W : Set X))
    (subordinate : ∀ W ∈ members, ∃ i, (W : Set X) ⊆ V i) :
    FiniteCoverRefinement U V where
  members := members
  cover := cover
  subordinate := subordinate

/-- The selected compact opens have compact pairwise intersections. -/
def HasCompactIntersections (R : FiniteCoverRefinement U V) : Prop :=
  ∀ W ∈ R.members, ∀ W' ∈ R.members, IsCompact ((W : Set X) ∩ W')

end FiniteCoverRefinement

namespace FiniteCoverRefinement

/-- An open cover of a compact open in a prespectral space has a finite subordinate refinement by
compact opens. -/
theorem nonempty_of_cover
    [PrespectralSpace X] (U : CompactOpens X)
    {ι : Type v} (V : ι → Opens X) (hV : (U : Set X) ⊆ ⋃ i, (V i : Set X)) :
    Nonempty (FiniteCoverRefinement U V) := sorry

/-- In a quasi-separated prespectral space, the finite compact-open refinement of a cover can be
chosen with compact pairwise intersections. -/
@[stacks 0069 "finite subordinate compact-open coverings with compact overlaps"]
theorem exists_withCompactIntersections
    [PrespectralSpace X] [QuasiSeparatedSpace X] (U : CompactOpens X)
    {ι : Type v} (V : ι → Opens X) (hV : (U : Set X) ⊆ ⋃ i, (V i : Set X)) :
    ∃ R : FiniteCoverRefinement U V, R.HasCompactIntersections := sorry

end FiniteCoverRefinement

end CompactOpens
