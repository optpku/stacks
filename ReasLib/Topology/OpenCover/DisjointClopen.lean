/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Separation.DisjointCover

/-!
# Finite disjoint clopen cover refinements

Finite pairwise disjoint clopen decompositions refining arbitrary open covers.
-/

@[expose] public section

open Set Topology TopologicalSpace
open scoped Function

universe u

/-- Every open cover of a topological space admits a finite pairwise disjoint
clopen refinement covering the space. -/
def HasFiniteDisjointClopenCoverRefinement (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ {ι : Type u} {U : ι → Opens X}, IsOpenCover U →
    ∃ (count : ℕ) (V : Fin count → Clopens X),
      Pairwise (Disjoint on V) ∧ IsOpenCover (fun index ↦ (V index).toOpens) ∧
        ∀ index, ∃ coverIndex, (V index : Set X) ⊆ (U coverIndex : Set X)

/-- The finite disjoint clopen cover-refinement criterion can be expressed with
explicit cover index and family binders. -/
theorem hasFiniteDisjointClopenCoverRefinement_iff {X : Type u} [TopologicalSpace X] :
    HasFiniteDisjointClopenCoverRefinement X ↔
      ∀ (ι : Type u) (U : ι → Opens X), IsOpenCover U →
        ∃ (count : ℕ) (V : Fin count → Clopens X),
          Pairwise (Disjoint on V) ∧ IsOpenCover (fun index ↦ (V index).toOpens) ∧
            ∀ index, ∃ coverIndex, (V index : Set X) ⊆ (U coverIndex : Set X) := sorry

namespace HasFiniteDisjointClopenCoverRefinement

/-- Every open cover of a space with the finite disjoint clopen cover-refinement
property has a finite pairwise disjoint clopen refinement covering the space. -/
theorem exists_clopen_cover {X : Type u} [TopologicalSpace X]
    (h : HasFiniteDisjointClopenCoverRefinement X) {ι : Type u} {U : ι → Opens X}
    (hU : IsOpenCover U) :
    ∃ (count : ℕ) (V : Fin count → Clopens X),
      Pairwise (Disjoint on V) ∧ IsOpenCover (fun index ↦ (V index).toOpens) ∧
        ∀ index, ∃ coverIndex, (V index : Set X) ⊆ (U coverIndex : Set X) := sorry

end HasFiniteDisjointClopenCoverRefinement

/-- Compact Hausdorff totally disconnected spaces have finite pairwise disjoint
clopen refinements of every open cover. -/
theorem hasFiniteDisjointClopenCoverRefinement_of_totallyDisconnected
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    HasFiniteDisjointClopenCoverRefinement X := sorry
