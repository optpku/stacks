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
    IsFiniteUnionOfLocallyClosed E := sorry

namespace IsFiniteUnionOfLocallyClosed

/-- The empty set is a finite union of locally closed subsets. -/
@[simp] theorem empty : IsFiniteUnionOfLocallyClosed (∅ : Set X) := sorry

/-- The whole space is a finite union of locally closed subsets. -/
@[simp] theorem univ : IsFiniteUnionOfLocallyClosed (univ : Set X) := sorry

/-- Finite unions of locally closed subsets are stable under binary union. -/
theorem union {E F : Set X} (hE : IsFiniteUnionOfLocallyClosed E)
    (hF : IsFiniteUnionOfLocallyClosed F) : IsFiniteUnionOfLocallyClosed (E ∪ F) := sorry

/-- Finite indexed unions preserve finite unions of locally closed subsets. -/
theorem iUnion {ι : Type*} [Finite ι] {E : ι → Set X}
    (hE : ∀ i, IsFiniteUnionOfLocallyClosed (E i)) :
    IsFiniteUnionOfLocallyClosed (⋃ i, E i) := sorry

/-- A finite indexed union of locally closed subsets is a finite union of locally closed subsets. -/
theorem iUnion_of_isLocallyClosed {ι : Type*} [Finite ι] {E : ι → Set X}
    (hE : ∀ i, IsLocallyClosed (E i)) :
    IsFiniteUnionOfLocallyClosed (⋃ i, E i) := sorry

/-- A union over a finite subset of an arbitrary index type preserves finite unions of locally
closed subsets. -/
theorem biUnion {ι : Type*} {E : ι → Set X} {s : Set ι} (hs : s.Finite)
    (hE : ∀ i ∈ s, IsFiniteUnionOfLocallyClosed (E i)) :
    IsFiniteUnionOfLocallyClosed (⋃ i ∈ s, E i) := sorry

/-- A union over a finite subset of locally closed subsets is a finite union of locally closed
subsets. -/
theorem biUnion_of_isLocallyClosed {ι : Type*} {E : ι → Set X} {s : Set ι} (hs : s.Finite)
    (hE : ∀ i ∈ s, IsLocallyClosed (E i)) :
    IsFiniteUnionOfLocallyClosed (⋃ i ∈ s, E i) := sorry

/-- The union of a finite family of finite unions of locally closed subsets is again a finite
union of locally closed subsets. -/
theorem sUnion {S : Set (Set X)} (hS : S.Finite)
    (hS' : ∀ E ∈ S, IsFiniteUnionOfLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed (⋃₀ S) := sorry

/-- The union of a finite family of locally closed subsets is a finite union of locally closed
subsets. -/
theorem sUnion_of_isLocallyClosed {S : Set (Set X)} (hS : S.Finite)
    (hS' : ∀ E ∈ S, IsLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed (⋃₀ S) := sorry

/-- Unpack a finite union of locally closed subsets into a `Fin n`-indexed locally closed family.

The result is enumeration-shaped for consumers that need induction on a finite decomposition,
while the core predicate itself remains free of noncanonical `Fintype` choices. -/
theorem exists_eq_iUnion {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    ∃ n : ℕ, ∃ S : Fin n → Set X, (∀ i, IsLocallyClosed (S i)) ∧ E = ⋃ i, S i := sorry

/-- Finite unions of locally closed subsets are stable under binary intersection. -/
theorem inter {E F : Set X} (hE : IsFiniteUnionOfLocallyClosed E)
    (hF : IsFiniteUnionOfLocallyClosed F) : IsFiniteUnionOfLocallyClosed (E ∩ F) := sorry

/-- Finite indexed intersections preserve finite unions of locally closed subsets. -/
theorem iInter {ι : Type*} [Finite ι] {E : ι → Set X}
    (hE : ∀ i, IsFiniteUnionOfLocallyClosed (E i)) :
    IsFiniteUnionOfLocallyClosed (⋂ i, E i) := sorry

/-- A finite intersection over an arbitrary finite index subset preserves finite unions of locally
closed subsets. -/
theorem biInter {ι : Type*} {E : ι → Set X} {s : Set ι} (hs : s.Finite)
    (hE : ∀ i ∈ s, IsFiniteUnionOfLocallyClosed (E i)) :
    IsFiniteUnionOfLocallyClosed (⋂ i ∈ s, E i) := sorry

/-- The intersection of a finite family of finite unions of locally closed subsets is again a
finite union of locally closed subsets. -/
theorem sInter {S : Set (Set X)} (hS : S.Finite)
    (hS' : ∀ E ∈ S, IsFiniteUnionOfLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed (⋂₀ S) := sorry

/-- Images along an inducing map with locally closed range preserve finite unions of locally
closed subsets. -/
theorem image {Y : Type v} [TopologicalSpace Y] {f : X → Y} {E : Set X}
    (hE : IsFiniteUnionOfLocallyClosed E) (hf : IsInducing f)
    (h_range : IsLocallyClosed (range f)) :
    IsFiniteUnionOfLocallyClosed (f '' E) := sorry

/-- Continuous preimages preserve finite unions of locally closed subsets. -/
theorem preimage {Y : Type v} [TopologicalSpace Y] {f : Y → X}
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) (hf : Continuous f) :
    IsFiniteUnionOfLocallyClosed (f ⁻¹' E) := sorry

/-- The complement of a locally closed subset is a finite union of locally closed subsets. -/
theorem compl_of_isLocallyClosed {E : Set X} (hE : IsLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed Eᶜ := sorry

/-- Complements of finite indexed unions of locally closed subsets are finite unions of locally
closed subsets. -/
theorem compl_iUnion {n : ℕ} {S : Fin n → Set X} (hS : ∀ i, IsLocallyClosed (S i)) :
    IsFiniteUnionOfLocallyClosed (⋃ i, S i)ᶜ := sorry

/-- Finite unions of locally closed subsets are stable under complement. -/
theorem compl {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed Eᶜ := sorry

/-- Finite unions of locally closed subsets are stable under set difference. -/
theorem sdiff {E F : Set X} (hE : IsFiniteUnionOfLocallyClosed E)
    (hF : IsFiniteUnionOfLocallyClosed F) :
    IsFiniteUnionOfLocallyClosed (E \ F) := sorry

end IsFiniteUnionOfLocallyClosed

end
