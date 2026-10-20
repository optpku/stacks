module

public import ReasLib.Topology.Stratification.Partition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Frontier conditions on locally closed partitions
-/

@[expose] public section

universe u

open Set TopologicalSpace

namespace LocallyClosedPartition

variable {X : Type u} [TopologicalSpace X]

/-- A locally closed partition satisfies the frontier condition when a part meeting the closure of
another is contained in that closure. -/
@[stacks 09Y0 "good stratifications"]
structure IsGood (P : LocallyClosedPartition X) : Prop where
  /-- A part meeting the closure of another part lies in that closure. -/
  frontier_condition (S T : P.toSet) (hST : ((S : Set X) ∩ closure (T : Set X)).Nonempty) :
    (S : Set X) ⊆ closure (T : Set X)

/-- The frontier-condition characterization of a good locally closed partition. -/
theorem isGood_iff (P : LocallyClosedPartition X) :
    P.IsGood ↔
      ∀ (S T : P.toSet), ((S : Set X) ∩ closure (T : Set X)).Nonempty →
        (S : Set X) ⊆ closure (T : Set X) := sorry

end LocallyClosedPartition
