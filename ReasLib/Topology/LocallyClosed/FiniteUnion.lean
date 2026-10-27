/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.LocallyClosed

/-!
# Finite unions of locally closed subsets

This module owns the Boolean-finite closure of `IsLocallyClosed` inside an
arbitrary topological space.  The core predicate uses a `Set.Finite` family,
so consumers with a finite subset of an ambient index type do not need to
choose an enumeration or install a `Fintype` instance.
-/

@[expose] public section

universe u v

open Set TopologicalSpace Topology
open scoped Set.Notation

section

variable {X : Type u} [TopologicalSpace X]

/-- A subset is a union of a finite family of locally closed subsets. -/
@[stacks 005Z "finite unions of locally closed subsets"]
def IsFiniteUnionOfLocallyClosed (E : Set X) : Prop :=
  ∃ S : Set (Set X), S.Finite ∧ (∀ Z ∈ S, IsLocallyClosed Z) ∧ E = ⋃₀ S

/-- A locally closed subset is a finite union of locally closed subsets with one piece. -/
theorem IsLocallyClosed.isFiniteUnionOfLocallyClosed {E : Set X} (hE : IsLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed E := by
  exact ⟨{E}, finite_singleton E, by simpa using hE, by simp⟩

namespace IsFiniteUnionOfLocallyClosed

/-- The empty set is a finite union of locally closed subsets. -/
@[simp] theorem empty : IsFiniteUnionOfLocallyClosed (∅ : Set X) := by
  exact isOpen_empty.isLocallyClosed.isFiniteUnionOfLocallyClosed

/-- The whole space is a finite union of locally closed subsets. -/
@[simp] theorem univ : IsFiniteUnionOfLocallyClosed (univ : Set X) := by
  exact isOpen_univ.isLocallyClosed.isFiniteUnionOfLocallyClosed

/-- Finite unions of locally closed subsets are stable under binary union. -/
theorem union {E F : Set X} (hE : IsFiniteUnionOfLocallyClosed E)
    (hF : IsFiniteUnionOfLocallyClosed F) : IsFiniteUnionOfLocallyClosed (E ∪ F) := by
  rcases hE with ⟨S, hS, hS', rfl⟩
  rcases hF with ⟨T, hT, hT', rfl⟩
  refine ⟨S ∪ T, hS.union hT, ?_, (sUnion_union S T).symm⟩
  intro Z hZ
  rcases hZ with hZ | hZ
  · exact hS' Z hZ
  · exact hT' Z hZ

/-- Finite indexed unions preserve finite unions of locally closed subsets. -/
theorem iUnion {ι : Type*} [Finite ι] {E : ι → Set X}
    (hE : ∀ i, IsFiniteUnionOfLocallyClosed (E i)) :
    IsFiniteUnionOfLocallyClosed (⋃ i, E i) := by
  have h : ∀ s : Set ι, s.Finite → IsFiniteUnionOfLocallyClosed (⋃ i ∈ s, E i) := by
    intro s hs
    induction s, hs using Set.Finite.induction_on with
    | empty => simpa using (empty (X := X))
    | @insert i s hi hs ih =>
      simpa only [Set.biUnion_insert] using (hE i).union ih
  simpa only [Set.biUnion_univ] using h Set.univ finite_univ

/-- A finite indexed union of locally closed subsets is a finite union of locally closed subsets. -/
theorem iUnion_of_isLocallyClosed {ι : Type*} [Finite ι] {E : ι → Set X}
    (hE : ∀ i, IsLocallyClosed (E i)) :
    IsFiniteUnionOfLocallyClosed (⋃ i, E i) := by
  exact iUnion fun i => (hE i).isFiniteUnionOfLocallyClosed

/-- A union over a finite subset of an arbitrary index type preserves finite unions of locally
closed subsets. -/
theorem biUnion {ι : Type*} {E : ι → Set X} {s : Set ι} (hs : s.Finite)
    (hE : ∀ i ∈ s, IsFiniteUnionOfLocallyClosed (E i)) :
    IsFiniteUnionOfLocallyClosed (⋃ i ∈ s, E i) := by
  haveI := hs.to_subtype
  simpa only [Set.iUnion_subtype] using iUnion (fun i : s => hE i i.property)

/-- A union over a finite subset of locally closed subsets is a finite union of locally closed
subsets. -/
theorem biUnion_of_isLocallyClosed {ι : Type*} {E : ι → Set X} {s : Set ι} (hs : s.Finite)
    (hE : ∀ i ∈ s, IsLocallyClosed (E i)) :
    IsFiniteUnionOfLocallyClosed (⋃ i ∈ s, E i) := by
  exact biUnion hs fun i hi => (hE i hi).isFiniteUnionOfLocallyClosed

/-- The union of a finite family of finite unions of locally closed subsets is again a finite
union of locally closed subsets. -/
theorem sUnion {S : Set (Set X)} (hS : S.Finite)
    (hS' : ∀ E ∈ S, IsFiniteUnionOfLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed (⋃₀ S) := by
  rw [Set.sUnion_eq_biUnion]
  exact biUnion hS hS'

/-- The union of a finite family of locally closed subsets is a finite union of locally closed
subsets. -/
theorem sUnion_of_isLocallyClosed {S : Set (Set X)} (hS : S.Finite)
    (hS' : ∀ E ∈ S, IsLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed (⋃₀ S) := by
  exact ⟨S, hS, hS', rfl⟩

/-- Unpack a finite union of locally closed subsets into a `Fin n`-indexed locally closed family.

The result is enumeration-shaped for consumers that need induction on a finite decomposition,
while the core predicate itself remains free of noncanonical `Fintype` choices. -/
theorem exists_eq_iUnion {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    ∃ n : ℕ, ∃ S : Fin n → Set X, (∀ i, IsLocallyClosed (S i)) ∧ E = ⋃ i, S i := by
  rcases hE with ⟨S, hS, hS', rfl⟩
  haveI := hS.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  refine ⟨n, fun i => (e.symm i).val, fun i => hS' _ (e.symm i).property, ?_⟩
  rw [Set.sUnion_eq_iUnion]
  exact (e.symm.surjective.iUnion_comp (fun Z : S => (Z : Set X))).symm

/-- Finite unions of locally closed subsets are stable under binary intersection. -/
theorem inter {E F : Set X} (hE : IsFiniteUnionOfLocallyClosed E)
    (hF : IsFiniteUnionOfLocallyClosed F) : IsFiniteUnionOfLocallyClosed (E ∩ F) := by
  rcases hE with ⟨S, hS, hS', rfl⟩
  rcases hF with ⟨T, hT, hT', rfl⟩
  rw [Set.sUnion_inter_sUnion]
  exact biUnion (hS.prod hT) fun p hp =>
    ((hS' p.1 hp.1).inter (hT' p.2 hp.2)).isFiniteUnionOfLocallyClosed

/-- Finite indexed intersections preserve finite unions of locally closed subsets. -/
theorem iInter {ι : Type*} [Finite ι] {E : ι → Set X}
    (hE : ∀ i, IsFiniteUnionOfLocallyClosed (E i)) :
    IsFiniteUnionOfLocallyClosed (⋂ i, E i) := by
  have h : ∀ s : Set ι, s.Finite → IsFiniteUnionOfLocallyClosed (⋂ i ∈ s, E i) := by
    intro s hs
    induction s, hs using Set.Finite.induction_on with
    | empty => simpa using (univ (X := X))
    | @insert i s hi hs ih =>
      simpa only [Set.biInter_insert] using (hE i).inter ih
  simpa only [Set.biInter_univ] using h Set.univ finite_univ

/-- A finite intersection over an arbitrary finite index subset preserves finite unions of locally
closed subsets. -/
theorem biInter {ι : Type*} {E : ι → Set X} {s : Set ι} (hs : s.Finite)
    (hE : ∀ i ∈ s, IsFiniteUnionOfLocallyClosed (E i)) :
    IsFiniteUnionOfLocallyClosed (⋂ i ∈ s, E i) := by
  haveI := hs.to_subtype
  simpa only [Set.iInter_subtype] using iInter (fun i : s => hE i i.property)

/-- The intersection of a finite family of finite unions of locally closed subsets is again a
finite union of locally closed subsets. -/
theorem sInter {S : Set (Set X)} (hS : S.Finite)
    (hS' : ∀ E ∈ S, IsFiniteUnionOfLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed (⋂₀ S) := by
  rw [Set.sInter_eq_biInter]
  exact biInter hS hS'

/-- Images along an inducing map with locally closed range preserve finite unions of locally
closed subsets. -/
theorem image {Y : Type v} [TopologicalSpace Y] {f : X → Y} {E : Set X}
    (hE : IsFiniteUnionOfLocallyClosed E) (hf : IsInducing f)
    (h_range : IsLocallyClosed (range f)) :
    IsFiniteUnionOfLocallyClosed (f '' E) := by
  obtain ⟨n, S, hS, rfl⟩ := hE.exists_eq_iUnion
  rw [Set.image_iUnion]
  exact iUnion_of_isLocallyClosed fun i => (hS i).image hf h_range

/-- Continuous preimages preserve finite unions of locally closed subsets. -/
theorem preimage {Y : Type v} [TopologicalSpace Y] {f : Y → X}
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) (hf : Continuous f) :
    IsFiniteUnionOfLocallyClosed (f ⁻¹' E) := by
  obtain ⟨n, S, hS, rfl⟩ := hE.exists_eq_iUnion
  rw [Set.preimage_iUnion]
  exact iUnion_of_isLocallyClosed fun i => (hS i).preimage hf

/-- The complement of a locally closed subset is a finite union of locally closed subsets. -/
theorem compl_of_isLocallyClosed {E : Set X} (hE : IsLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed Eᶜ := by
  rcases hE with ⟨U, Z, hU, hZ, rfl⟩
  rw [Set.compl_inter]
  exact hU.isClosed_compl.isLocallyClosed.isFiniteUnionOfLocallyClosed.union
    hZ.isOpen_compl.isLocallyClosed.isFiniteUnionOfLocallyClosed

/-- Complements of finite indexed unions of locally closed subsets are finite unions of locally
closed subsets. -/
theorem compl_iUnion {n : ℕ} {S : Fin n → Set X} (hS : ∀ i, IsLocallyClosed (S i)) :
    IsFiniteUnionOfLocallyClosed (⋃ i, S i)ᶜ := by
  rw [Set.compl_iUnion]
  exact iInter fun i => compl_of_isLocallyClosed (hS i)

/-- Finite unions of locally closed subsets are stable under complement. -/
theorem compl {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed Eᶜ := by
  obtain ⟨n, S, hS, rfl⟩ := hE.exists_eq_iUnion
  exact compl_iUnion hS

/-- Finite unions of locally closed subsets are stable under set difference. -/
theorem sdiff {E F : Set X} (hE : IsFiniteUnionOfLocallyClosed E)
    (hF : IsFiniteUnionOfLocallyClosed F) :
    IsFiniteUnionOfLocallyClosed (E \ F) := by
  exact hE.inter hF.compl

end IsFiniteUnionOfLocallyClosed

end
