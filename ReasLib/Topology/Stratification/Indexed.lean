/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Setoid.Partition
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Stratification.Partition

/-!
# Indexed locally closed stratifications

An indexed stratification permits empty indexed strata.  The canonical partition views discard
those redundant indices while retaining the original ordered family for closure arguments.
-/

@[expose] public section

universe u v

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- An ordered, locally closed, pairwise-disjoint cover whose closures are unions of lower
strata. -/
@[stacks 09Y1 "indexed locally closed stratifications"]
structure IsStratification {I : Type v} [PartialOrder I] (strata : I → Set X) : Prop where
  /-- Distinct strata are disjoint. -/
  disjoint : Pairwise fun i j ↦ Disjoint (strata i) (strata j)
  /-- The strata cover the ambient space. -/
  cover : (⋃ i, strata i) = univ
  /-- Each stratum is locally closed. -/
  locallyClosed : ∀ i, IsLocallyClosed (strata i)
  /-- The closure of a stratum is contained in the union of lower strata. -/
  closure_subset : ∀ j, closure (strata j) ⊆ ⋃ i ∈ Set.Iic j, strata i

/-- The four defining conditions for an indexed locally closed stratification. -/
theorem isStratification_iff {I : Type v} [PartialOrder I] (strata : I → Set X) :
    IsStratification strata ↔
      Pairwise (fun i j ↦ Disjoint (strata i) (strata j)) ∧
      (⋃ i, strata i) = univ ∧
      (∀ i, IsLocallyClosed (strata i)) ∧
      ∀ j, closure (strata j) ⊆ ⋃ i ∈ Set.Iic j, strata i := sorry

namespace IsStratification

variable {I : Type v} [PartialOrder I] {strata : I → Set X}

/-- The indices of the nonempty strata. -/
abbrev NonemptyIndex (strata : I → Set X) :=
  { i : I // (strata i).Nonempty }

/-- The family obtained by discarding empty indexed strata. -/
abbrev nonemptyStrata (strata : I → Set X) : NonemptyIndex strata → Set X :=
  fun i ↦ strata i.1

/-- Nonempty strata remain pairwise disjoint. -/
theorem nonemptyStrata_pairwiseDisjoint (h : IsStratification strata) :
    Pairwise fun i j : NonemptyIndex strata ↦
      Disjoint (nonemptyStrata strata i) (nonemptyStrata strata j) := sorry

/-- Every point belongs to a nonempty stratum. -/
theorem exists_mem_nonemptyStrata (h : IsStratification strata) (x : X) :
    ∃ i : NonemptyIndex strata, x ∈ nonemptyStrata strata i := sorry

/-- The indexed partition obtained by deleting empty strata. -/
noncomputable def toIndexedPartition (h : IsStratification strata) :
    IndexedPartition (nonemptyStrata strata) :=
  IndexedPartition.mk' (nonemptyStrata strata) h.nonemptyStrata_pairwiseDisjoint
    (fun i ↦ i.2) h.exists_mem_nonemptyStrata

/-- Two strata containing the same point have equal indices. -/
theorem eq_of_mem (h : IsStratification strata) {i j : I} {x : X}
    (hxi : x ∈ strata i) (hxj : x ∈ strata j) :
    i = j := sorry

/-- If one stratum meets the closure of another, its index is below the latter's index. -/
theorem le_of_inter_closure_nonempty (h : IsStratification strata) {i j : I}
    (hij : ((strata i) ∩ closure (strata j)).Nonempty) : i ≤ j := sorry

/-- The nonempty strata form a set-theoretic partition. -/
theorem range_nonemptyStrata_isPartition (h : IsStratification strata) :
    Setoid.IsPartition (Set.range (nonemptyStrata strata)) := sorry

/-- The underlying set-theoretic partition of an indexed stratification. -/
noncomputable def toPartitions (h : IsStratification strata) : Setoid.Partitions X :=
  ⟨Set.range (nonemptyStrata strata), h.range_nonemptyStrata_isPartition⟩

/-- A part of the underlying partition of an indexed stratification is locally closed. -/
theorem locallyClosed_of_mem_toPartitions (h : IsStratification strata)
    {s : Set X} (hs : s ∈ h.toPartitions.toSet) :
    IsLocallyClosed s := sorry

/-- The locally closed partition obtained by forgetting the indexing of nonempty strata. -/
noncomputable def toLocallyClosedPartition
    (h : IsStratification strata) : LocallyClosedPartition X where
  toPartitions := h.toPartitions
  locallyClosed s := h.locallyClosed_of_mem_toPartitions s.2

/-- The parts of the induced locally closed partition are the nonempty strata. -/
@[simp]
theorem toLocallyClosedPartition_toSet (h : IsStratification strata) :
    h.toLocallyClosedPartition.toSet = Set.range (nonemptyStrata strata) := sorry

/-- A subset is a part of the induced locally closed partition precisely when it is a nonempty
value of the original family. -/
@[simp]
theorem mem_toLocallyClosedPartition_iff (h : IsStratification strata) {s : Set X} :
    s ∈ h.toLocallyClosedPartition.toSet ↔
      ∃ i : I, (strata i).Nonempty ∧ strata i = s := sorry

/-- Every nonempty original stratum occurs in the induced locally closed partition. -/
theorem mem_toLocallyClosedPartition (h : IsStratification strata) (i : I)
    (hi : (strata i).Nonempty) :
    strata i ∈ h.toLocallyClosedPartition.toSet := sorry

end IsStratification

/-- A finite indexed locally closed stratification, with its indexing data available for direct
downstream use. -/
@[stacks 09Y3 "finite stratifications"]
structure FiniteStratification (X : Type u) [TopologicalSpace X] where
  /-- The finite ordered index type. -/
  index : Type v
  /-- Finiteness of the index type. -/
  instFinite : Finite index
  /-- The order controlling frontier relations. -/
  instPartialOrder : PartialOrder index
  /-- The indexed family of strata. -/
  strata : index → Set X
  /-- The stratification conditions on the family of strata. -/
  isStratification : @IsStratification X _ index instPartialOrder strata

namespace FiniteStratification

variable {X : Type u} [TopologicalSpace X]

/-- Construct a finite stratification from a finite ordered family satisfying the stratification
conditions. -/
def ofStrata {I : Type v} [Finite I] [PartialOrder I] (strata : I → Set X)
    (hstrata : IsStratification strata) : FiniteStratification X where
  index := I
  instFinite := inferInstance
  instPartialOrder := inferInstance
  strata := strata
  isStratification := hstrata

/-- The locally closed partition obtained by forgetting the finite indexing of a stratification. -/
noncomputable def toLocallyClosedPartition (S : FiniteStratification X) :
    LocallyClosedPartition X :=
  @IsStratification.toLocallyClosedPartition X _ S.index S.instPartialOrder S.strata
    S.isStratification

/-- The locally closed partition underlying a finite stratification has finitely many parts. -/
theorem toLocallyClosedPartition_finite (S : FiniteStratification X) :
    S.toLocallyClosedPartition.toSet.Finite := sorry

end FiniteStratification

/-- The one-stratum family is an indexed stratification. -/
theorem oneStratum_isStratification :
    IsStratification (fun _ : Fin 1 ↦ (univ : Set X)) := sorry
