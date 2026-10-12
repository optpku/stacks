/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
import Mathlib.Tactic.CrossRefAttribute

/-!
# Baire topological additive groups

This leaf packages the passage from completeness and a countably generated
neighborhood filter at zero to the canonical `BaireSpace` API.

@stack 0CQU
-/

@[expose] public section

open scoped Topology

universe u

section TopologicalAddGroup

variable {M : Type u} [TopologicalSpace M]
variable [addGroup : AddGroup M] [topologicalAddGroup : IsTopologicalAddGroup M]
variable [countablyGenerated : (nhds (0 : M)).IsCountablyGenerated]
variable [completeSpace : @CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M)]

include addGroup topologicalAddGroup countablyGenerated completeSpace

/-- A complete topological additive group with countably generated `nhds 0` is a Baire space. -/
theorem baireSpace_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup :
    BaireSpace M := sorry

attribute [instance 100] baireSpace_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup

/-- In a complete topological additive group with countably generated `nhds 0`, a countable
intersection of open dense subsets is dense. -/
theorem dense_iInter_open_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup
    {U : ℕ+ → Set M} (hU_open : ∀ n, IsOpen (U n)) (hU_dense : ∀ n, Dense (U n)) :
    Dense (⋂ n, U n) := sorry

end TopologicalAddGroup

section LinearTopology

variable {M : Type u} [TopologicalSpace M]
variable [addCommGroup : AddCommGroup M] [topologicalAddGroup : IsTopologicalAddGroup M]
variable [linearTopology : IsLinearTopology ℤ M]
variable [countablyGenerated : (nhds (0 : M)).IsCountablyGenerated]
variable [completeSpace : @CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M)]

include addCommGroup topologicalAddGroup linearTopology countablyGenerated completeSpace

/-- Lemma 15.36.3 (Baire category theorem) (0CQU): in a complete linearly topologized
abelian group with a countable fundamental system of neighborhoods of zero, the intersection of
countably many open dense subsets is dense. -/
@[stacks 0CQU "Baire category theorem"]
theorem dense_iInter_open_of_complete_linearlyTopologizedAddGroup
    {U : ℕ+ → Set M} (hU_open : ∀ n, IsOpen (U n)) (hU_dense : ∀ n, Dense (U n)) :
    Dense (⋂ n, U n) := sorry

namespace AddSubgroup

/-- Lemma 15.36.4 (0CQV): if a complete linearly topologized abelian group with a
countable fundamental system of neighborhoods of zero is covered by countably many closed
additive subgroups, then one of those subgroups is open. -/
@[stacks 0CQV]
theorem exists_isOpen_of_iUnion_eq_univ
    (N : ℕ+ → AddSubgroup M) (hN_closed : ∀ n, IsClosed (N n : Set M))
    (hcover : (⋃ n, (N n : Set M)) = Set.univ) :
    ∃ n, IsOpen (N n : Set M) := sorry

end AddSubgroup

end LinearTopology
