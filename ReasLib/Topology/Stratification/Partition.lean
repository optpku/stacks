/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Setoid.Partition
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Separation.Basic

/-!
# Locally closed partitions

This module refines Mathlib's `Setoid.Partitions` with the topological condition that every
part is locally closed.  The underlying partition remains directly accessible, so ordinary
partition and refinement APIs continue to apply.
-/

@[expose] public section

universe u

open Set

/-- A partition of a topological space whose parts are all locally closed. -/
@[stacks 09XZ "locally closed parts"]
structure LocallyClosedPartition (X : Type u) [TopologicalSpace X] where
  /-- The underlying set-theoretic partition. -/
  toPartitions : Setoid.Partitions X
  /-- Every part of the underlying partition is locally closed. -/
  locallyClosed (s : toPartitions.toSet) : IsLocallyClosed (s : Set X)

namespace LocallyClosedPartition

variable {X : Type u} [TopologicalSpace X]

/-- The set of parts of a locally closed partition. -/
abbrev toSet (P : LocallyClosedPartition X) : Set (Set X) :=
  P.toPartitions.toSet

/-- Two locally closed partitions are equal if they have the same parts. -/
@[ext]
theorem ext {P Q : LocallyClosedPartition X} (h : P.toSet = Q.toSet) : P = Q := sorry

/-- A part of a locally closed partition is locally closed as a subset of the ambient space. -/
theorem locallyClosed_of_mem (P : LocallyClosedPartition X) {s : Set X} (hs : s ∈ P.toSet) :
    IsLocallyClosed s :=
  P.locallyClosed ⟨s, hs⟩

/-- The parts of a locally closed partition form a set-theoretic partition. -/
theorem isPartition (P : LocallyClosedPartition X) : Setoid.IsPartition P.toSet :=
  P.toPartitions.isPartition

/-- The refinement partial order on locally closed partitions, induced by their underlying
set-theoretic partitions. -/
@[reducible]
def refinementOrder : PartialOrder (LocallyClosedPartition X) :=
  PartialOrder.lift toPartitions fun _ _ h ↦
    ext <| Setoid.Partitions.ext_iff _ _ |>.1 h

/-- `P.Refines Q` means that `P` refines `Q` in the explicit refinement order. -/
def Refines (P Q : LocallyClosedPartition X) : Prop :=
  (refinementOrder (X := X)).le P Q

/-- The partition of a `T₁` space into singleton locally closed parts. -/
def singletons (X : Type u) [TopologicalSpace X] [T1Space X] : LocallyClosedPartition X where
  toPartitions := ⊥
  locallyClosed _ := sorry

/-- The parts of the singleton partition are exactly the singleton subsets. -/
@[simp]
theorem mem_singletons_toSet_iff [T1Space X] {s : Set X} :
    s ∈ (singletons X).toSet ↔ ∃ x : X, s = ({x} : Set X) := sorry

/-- A locally closed partition refines another precisely when every one of its parts is contained
in a part of the latter. -/
@[stacks 09XZ "refinement of partitions"]
theorem refines_iff_forall_exists_mem_subset {P Q : LocallyClosedPartition X} :
    P.Refines Q ↔ ∀ ⦃s : Set X⦄, s ∈ P.toSet → ∃ t ∈ Q.toSet, s ⊆ t := sorry

end LocallyClosedPartition
