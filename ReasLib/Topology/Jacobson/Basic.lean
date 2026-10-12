/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Spectral.Prespectral
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic Jacobson-Space Criteria

This leaf contains topology-only criteria for the Jacobson property and a
consequence of its failure. Constructible closed-point trace API lives in
sibling leaves.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

namespace PrespectralSpace

variable {X : Type u} [TopologicalSpace X] [T0Space X] [PrespectralSpace X]

/-- Lemma 5.18.3: a non-Jacobson Kolmogorov prespectral space has a non-closed
point with locally closed singleton. -/
@[stacks 02I7]
theorem exists_nonclosedPoint_with_locallyClosedSingleton
    (h_notJacobson : ¬ JacobsonSpace X) :
    ∃ x, x ∉ closedPoints X ∧ IsLocallyClosed ({x} : Set X) := by
  rw [jacobsonSpace_iff_locallyClosed] at h_notJacobson
  push Not at h_notJacobson
  obtain ⟨Z, hZ, hZlocallyClosed, hZclosedPoints⟩ := h_notJacobson
  obtain ⟨U, C, hU, hC, rfl⟩ := hZlocallyClosed
  obtain ⟨x, hx⟩ := hZ
  obtain ⟨V, hV, hxV, hVU⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hx.1 hU
  have hVCnonempty : ((Subtype.val : V → X) ⁻¹' C).Nonempty :=
    ⟨⟨x, hxV⟩, hx.2⟩
  letI : CompactSpace V := isCompact_iff_compactSpace.mp hV.2
  obtain ⟨y, hyC, hyClosed⟩ :=
    (hC.preimage continuous_subtype_val).exists_closed_singleton hVCnonempty
  refine ⟨y, ?_, ?_⟩
  · intro hyClosedInX
    have hy : (y : X) ∈ (U ∩ C) ∩ closedPoints X :=
      ⟨⟨hVU y.2, hyC⟩, hyClosedInX⟩
    rw [hZclosedPoints] at hy
    exact hy
  · simpa using
      hyClosed.isLocallyClosed.image IsEmbedding.subtypeVal.isInducing
        hV.1.isOpenEmbedding_subtypeVal.isOpen_range.isLocallyClosed

end PrespectralSpace

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 5.18.2: a space is Jacobson exactly when closed points are dense in
the closure of every singleton. -/
@[stacks 005V]
theorem jacobsonSpace_iff_dense_closedPoints_in_singleton_closure :
    JacobsonSpace X ↔
      ∀ x : X,
        closure (closure ({x} : Set X) ∩ closedPoints X) = closure ({x} : Set X) := by
  constructor
  · intro h x
    letI : JacobsonSpace X := h
    exact closure_inter_closedPoints isClosed_closure
  · intro h
    constructor
    intro Z hZ
    apply Set.Subset.antisymm
    · exact hZ.closure_subset_iff.mpr Set.inter_subset_left
    · intro x hxZ
      have hxClosure : x ∈ closure ({x} : Set X) :=
        subset_closure (Set.mem_singleton x)
      have hxDense : x ∈ closure (closure ({x} : Set X) ∩ closedPoints X) := by
        rw [h x]
        exact hxClosure
      have hsingletonSubset : closure ({x} : Set X) ⊆ Z :=
        hZ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxZ)
      exact closure_mono
        (Set.inter_subset_inter hsingletonSubset Set.Subset.rfl) hxDense
