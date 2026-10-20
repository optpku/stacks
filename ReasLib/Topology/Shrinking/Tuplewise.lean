/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Shrinking.Basic

/-!
# Tuplewise shrinkings of open covers

Reusable data and existence statements for shrinking a compact normal open
cover while controlling every fixed finite intersection.
-/

@[expose] public section

open Set TopologicalSpace

universe u v w z

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- Lemma 5.13.5 (`09UW`) companion predicate: a tuplewise shrinking refinement
covers the ambient space, has closures inside the labelled original members,
and subordinates every realized tuple intersection to a prescribed open family. -/
@[stacks 09UW "tuplewise shrinking refinement predicate"]
structure IsTuplewiseShrinkingRefinement
    (U : ι → Opens X) (p : ℕ)
    {κ : (Fin (p + 1) → ι) → Type w}
    (W : ∀ s : Fin (p + 1) → ι, κ s → Opens X)
    {J : Type z} (V : J → Opens X) (α : J → ι) : Prop where
  /-- The refined family covers the ambient space. -/
  isOpenCover : IsOpenCover V
  /-- Each refined member has closure inside its labelled original member. -/
  closure_subset (j : J) : closure (V j) ⊆ (U (α j) : Set X)
  /-- A realized tuple intersection is empty or lies in one prescribed member. -/
  tuplewise_subordinate (jTuple : Fin (p + 1) → J) :
    (⋂ a : Fin (p + 1), (V (jTuple a) : Set X)) = ∅ ∨
      ∃ k : κ (fun a ↦ α (jTuple a)),
        (⋂ a : Fin (p + 1), (V (jTuple a) : Set X)) ⊆
          W (fun a ↦ α (jTuple a)) k

/-- The cover, closure-control, and tuplewise-subordination conditions for a
tuplewise shrinking refinement. -/
theorem isTuplewiseShrinkingRefinement_iff
    {U : ι → Opens X} (p : ℕ)
    {κ : (Fin (p + 1) → ι) → Type w}
    (W : ∀ s : Fin (p + 1) → ι, κ s → Opens X)
    {J : Type z} (V : J → Opens X) (α : J → ι) :
    IsTuplewiseShrinkingRefinement U p W V α ↔
      IsOpenCover V ∧
        (∀ j, closure (V j) ⊆ (U (α j) : Set X)) ∧
          ∀ jTuple : Fin (p + 1) → J,
            (⋂ a : Fin (p + 1), (V (jTuple a) : Set X)) = ∅ ∨
              ∃ k : κ (fun a ↦ α (jTuple a)),
                (⋂ a : Fin (p + 1), (V (jTuple a) : Set X)) ⊆
                  W (fun a ↦ α (jTuple a)) k := sorry

namespace IsOpenCover

section

variable [CompactSpace X] [NormalSpace X]

/-- A compact normal tuplewise shrinking refinement can be chosen with a canonical finite index.
This `Fin n` form avoids making downstream users install a local `Fintype` instance before using
the refinement in finite-intersection and nerve constructions. -/
@[stacks 09UW "finite tuplewise shrinking refinement in a compact normal space"]
theorem exists_finite_tuplewise_shrinking_refinement
    {U : ι → Opens X} (hU : IsOpenCover U) (p : ℕ)
    {κ : (Fin (p + 1) → ι) → Type w}
    (W : ∀ s : Fin (p + 1) → ι, κ s → Opens X)
    (hW_cover : ∀ s : Fin (p + 1) → ι,
      (⋂ a : Fin (p + 1), (U (s a) : Set X)) = ⋃ k, (W s k : Set X)) :
    ∃ (n : ℕ) (V : Fin n → Opens X) (α : Fin n → ι),
      IsTuplewiseShrinkingRefinement U p W V α := sorry

/-- Lemma 5.13.5 (`09UW`), generalized to compact normal spaces: an open cover
admits a tuplewise shrinking refinement subordinate to any prescribed covers of
its fixed-order intersections. -/
@[stacks 09UW "tuplewise shrinking refinement in a compact normal space"]
theorem exists_tuplewise_shrinking_refinement
    {U : ι → Opens X} (hU : IsOpenCover U) (p : ℕ)
    {κ : (Fin (p + 1) → ι) → Type w}
    (W : ∀ s : Fin (p + 1) → ι, κ s → Opens X)
    (hW_cover : ∀ s : Fin (p + 1) → ι,
      (⋂ a : Fin (p + 1), (U (s a) : Set X)) = ⋃ k, (W s k : Set X)) :
    ∃ (J : Type (max u v w)) (V : J → Opens X) (α : J → ι),
      IsTuplewiseShrinkingRefinement U p W V α := sorry

end

end IsOpenCover

end TopologicalSpace
