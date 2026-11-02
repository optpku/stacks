/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.LocallyClosed
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Arbitrary Unions of Locally Closed Subsets

This leaf owns the arbitrary, pointwise geometric notion of a union of
locally closed subsets.  It deliberately has no finite or constructible
dependency, so it can be used by local and geometric arguments on its own.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 5.18.5: a subset is a union of locally closed subsets when it is the
set union of some family of locally closed subsets. -/
@[stacks 005X]
def IsUnionOfLocallyClosed (T : Set X) : Prop :=
  ∃ S : Set (Set X), (∀ Z ∈ S, IsLocallyClosed Z) ∧ T = ⋃₀ S

/-- A subset is a union of locally closed subsets exactly when each of its
points lies in a locally closed subset contained in it. -/
@[stacks 005X]
theorem isUnionOfLocallyClosed_iff_forall_mem_exists {T : Set X} :
    IsUnionOfLocallyClosed T ↔
      ∀ x ∈ T, ∃ Z : Set X, IsLocallyClosed Z ∧ x ∈ Z ∧ Z ⊆ T := by
  constructor
  · show IsUnionOfLocallyClosed T →
      ∀ x ∈ T, ∃ Z : Set X, IsLocallyClosed Z ∧ x ∈ Z ∧ Z ⊆ T
    rintro ⟨S, hS, rfl⟩ x hx
    obtain ⟨Z, hZS, hxZ⟩ := mem_sUnion.mp hx
    exact ⟨Z, hS Z hZS, hxZ, subset_sUnion_of_mem hZS⟩
  · show (∀ x ∈ T, ∃ Z : Set X, IsLocallyClosed Z ∧ x ∈ Z ∧ Z ⊆ T) →
      IsUnionOfLocallyClosed T
    intro hT
    refine ⟨{Z | IsLocallyClosed Z ∧ Z ⊆ T}, fun Z hZ ↦ hZ.1, ?_⟩
    apply Subset.antisymm
    · show T ⊆ ⋃₀ {Z | IsLocallyClosed Z ∧ Z ⊆ T}
      intro x hx
      obtain ⟨Z, hZ, hxZ, hZT⟩ := hT x hx
      exact mem_sUnion_of_mem hxZ ⟨hZ, hZT⟩
    · show ⋃₀ {Z | IsLocallyClosed Z ∧ Z ⊆ T} ⊆ T
      intro x hx
      obtain ⟨Z, hZ, hxZ⟩ := mem_sUnion.mp hx
      exact hZ.2 hxZ

/-- A locally closed subset is a union of locally closed subsets. -/
theorem IsLocallyClosed.isUnionOfLocallyClosed {T : Set X} (hT : IsLocallyClosed T) :
    IsUnionOfLocallyClosed T := by
  apply isUnionOfLocallyClosed_iff_forall_mem_exists.mpr
  intro x hx
  exact ⟨T, hT, hx, Subset.rfl⟩

/-- The union of two unions of locally closed subsets is again such a union. -/
theorem IsUnionOfLocallyClosed.union {S T : Set X}
    (hS : IsUnionOfLocallyClosed S) (hT : IsUnionOfLocallyClosed T) :
    IsUnionOfLocallyClosed (S ∪ T) := by
  apply isUnionOfLocallyClosed_iff_forall_mem_exists.mpr
  intro x hx
  rcases hx with hx | hx
  · show ∃ Z : Set X, IsLocallyClosed Z ∧ x ∈ Z ∧ Z ⊆ S ∪ T
    obtain ⟨Z, hZ, hxZ, hZS⟩ := isUnionOfLocallyClosed_iff_forall_mem_exists.mp hS x hx
    exact ⟨Z, hZ, hxZ, hZS.trans subset_union_left⟩
  · show ∃ Z : Set X, IsLocallyClosed Z ∧ x ∈ Z ∧ Z ⊆ S ∪ T
    obtain ⟨Z, hZ, hxZ, hZT⟩ := isUnionOfLocallyClosed_iff_forall_mem_exists.mp hT x hx
    exact ⟨Z, hZ, hxZ, hZT.trans subset_union_right⟩

/-- An arbitrary union of unions of locally closed subsets is a union of locally closed subsets. -/
theorem IsUnionOfLocallyClosed.iUnion {ι : Type*} {T : ι → Set X}
    (hT : ∀ i, IsUnionOfLocallyClosed (T i)) :
    IsUnionOfLocallyClosed (⋃ i, T i) := by
  apply isUnionOfLocallyClosed_iff_forall_mem_exists.mpr
  intro x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
  obtain ⟨Z, hZ, hxZ, hZT⟩ := isUnionOfLocallyClosed_iff_forall_mem_exists.mp (hT i) x hxi
  exact ⟨Z, hZ, hxZ, hZT.trans (subset_iUnion T i)⟩

/-- A set-indexed union of unions of locally closed subsets is a union of locally closed subsets. -/
theorem IsUnionOfLocallyClosed.sUnion {S : Set (Set X)}
    (hS : ∀ T ∈ S, IsUnionOfLocallyClosed T) :
    IsUnionOfLocallyClosed (⋃₀ S) := by
  apply isUnionOfLocallyClosed_iff_forall_mem_exists.mpr
  intro x hx
  obtain ⟨T, hTS, hxT⟩ := mem_sUnion.mp hx
  obtain ⟨Z, hZ, hxZ, hZT⟩ := isUnionOfLocallyClosed_iff_forall_mem_exists.mp (hS T hTS) x hxT
  exact ⟨Z, hZ, hxZ, hZT.trans (subset_sUnion_of_mem hTS)⟩

/-- Intersecting two unions of locally closed subsets preserves the union-of-locally-closed
property. -/
theorem IsUnionOfLocallyClosed.inter {S T : Set X}
    (hS : IsUnionOfLocallyClosed S) (hT : IsUnionOfLocallyClosed T) :
    IsUnionOfLocallyClosed (S ∩ T) := by
  apply isUnionOfLocallyClosed_iff_forall_mem_exists.mpr
  intro x hx
  obtain ⟨Z, hZ, hxZ, hZS⟩ := isUnionOfLocallyClosed_iff_forall_mem_exists.mp hS x hx.1
  obtain ⟨W, hW, hxW, hWT⟩ := isUnionOfLocallyClosed_iff_forall_mem_exists.mp hT x hx.2
  exact ⟨Z ∩ W, hZ.inter hW, ⟨hxZ, hxW⟩, inter_subset_inter hZS hWT⟩

/-- A continuous preimage of a union of locally closed subsets is a union of locally closed
subsets. -/
theorem IsUnionOfLocallyClosed.preimage {Y : Type*} [TopologicalSpace Y]
    {T : Set X} (hT : IsUnionOfLocallyClosed T) {f : Y → X} (hf : Continuous f) :
    IsUnionOfLocallyClosed (f ⁻¹' T) := by
  apply isUnionOfLocallyClosed_iff_forall_mem_exists.mpr
  intro y hy
  obtain ⟨Z, hZ, hfyZ, hZT⟩ := isUnionOfLocallyClosed_iff_forall_mem_exists.mp hT (f y) hy
  exact ⟨f ⁻¹' Z, hZ.preimage hf, hfyZ, preimage_mono hZT⟩
