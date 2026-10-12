/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
      ∀ x ∈ T, ∃ Z : Set X, IsLocallyClosed Z ∧ x ∈ Z ∧ Z ⊆ T := sorry

/-- A locally closed subset is a union of locally closed subsets. -/
theorem IsLocallyClosed.isUnionOfLocallyClosed {T : Set X} (hT : IsLocallyClosed T) :
    IsUnionOfLocallyClosed T := sorry

/-- The union of two unions of locally closed subsets is again such a union. -/
theorem IsUnionOfLocallyClosed.union {S T : Set X}
    (hS : IsUnionOfLocallyClosed S) (hT : IsUnionOfLocallyClosed T) :
    IsUnionOfLocallyClosed (S ∪ T) := sorry

/-- An arbitrary union of unions of locally closed subsets is a union of locally closed subsets. -/
theorem IsUnionOfLocallyClosed.iUnion {ι : Type*} {T : ι → Set X}
    (hT : ∀ i, IsUnionOfLocallyClosed (T i)) :
    IsUnionOfLocallyClosed (⋃ i, T i) := sorry

/-- A set-indexed union of unions of locally closed subsets is a union of locally closed subsets. -/
theorem IsUnionOfLocallyClosed.sUnion {S : Set (Set X)}
    (hS : ∀ T ∈ S, IsUnionOfLocallyClosed T) :
    IsUnionOfLocallyClosed (⋃₀ S) := sorry

/-- Intersecting two unions of locally closed subsets preserves the union-of-locally-closed
property. -/
theorem IsUnionOfLocallyClosed.inter {S T : Set X}
    (hS : IsUnionOfLocallyClosed S) (hT : IsUnionOfLocallyClosed T) :
    IsUnionOfLocallyClosed (S ∩ T) := sorry

/-- A continuous preimage of a union of locally closed subsets is a union of locally closed
subsets. -/
theorem IsUnionOfLocallyClosed.preimage {Y : Type*} [TopologicalSpace Y]
    {T : Set X} (hT : IsUnionOfLocallyClosed T) {f : Y → X} (hf : Continuous f) :
    IsUnionOfLocallyClosed (f ⁻¹' T) := sorry
