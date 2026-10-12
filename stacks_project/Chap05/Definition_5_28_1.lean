/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Stratification.Partition
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 5.28.1: locally closed partitions are owned by the reusable topology API. -/
@[stacks 09XZ "locally closed parts"]
#check (LocallyClosedPartition : (X : Type u) → [TopologicalSpace X] → Type u)

/- The source refinement relation uses the explicit partition-refinement order. -/
#check (LocallyClosedPartition.refinementOrder :
  {X : Type u} → [TopologicalSpace X] → PartialOrder (LocallyClosedPartition X))

@[stacks 09XZ "refinement of partitions"]
#check (LocallyClosedPartition.refines_iff_forall_exists_mem_subset :
  ∀ {X : Type u} [TopologicalSpace X] {P Q : LocallyClosedPartition X},
    P.Refines Q ↔
      ∀ ⦃s : Set X⦄, s ∈ P.toSet → ∃ t ∈ Q.toSet, s ⊆ t)
