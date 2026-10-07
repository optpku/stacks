module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section

open scoped Topology

universe u

/-- A closed `p`-subgroup that is maximal among closed `p`-subgroups. -/
def IsMaximalProPSubgroup (p : ℕ) {G : Type u} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : Prop :=
  IsPGroup p H ∧ IsClosed (H : Set G) ∧
    ∀ K : Subgroup G, IsPGroup p K → IsClosed (K : Set G) → H ≤ K → K = H

namespace IsMaximalProPSubgroup

variable (p : ℕ) {G : Type u} [Group G] [TopologicalSpace G] {H : Subgroup G}

/-- A maximal pro-`p` subgroup is a `p`-group. -/
theorem isPGroup (hH : IsMaximalProPSubgroup p H) : IsPGroup p H := sorry

/-- A maximal pro-`p` subgroup is closed. -/
theorem isClosed (hH : IsMaximalProPSubgroup p H) : IsClosed (H : Set G) :=
  sorry

/-- A closed `p`-supergroup of a maximal pro-`p` subgroup equals it. -/
theorem eq_of_le (hH : IsMaximalProPSubgroup p H) {K : Subgroup G}
    (hK : IsPGroup p K) (hKcl : IsClosed (K : Set G)) (hHK : H ≤ K) : K = H :=
  sorry

/-- Unfolding of maximality among closed `p`-subgroups. -/
theorem iff :
    IsMaximalProPSubgroup p H ↔
      IsPGroup p H ∧ IsClosed (H : Set G) ∧
        ∀ K : Subgroup G, IsPGroup p K → IsClosed (K : Set G) → H ≤ K → K = H :=
  sorry

end IsMaximalProPSubgroup
