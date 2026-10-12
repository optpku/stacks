/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open normal subgroups

Reusable order-theoretic structure on open normal subgroups of a topological group.
Mathlib already supplies finite intersections; this file records the canonical whole-group
element, which makes the indexing type nonempty without a local choice or instance pin.
-/

@[expose] public section

universe u

namespace OpenNormalSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The whole group as an open normal subgroup. -/
@[stacks 0BR1 "whole open normal subgroup"]
def top : OpenNormalSubgroup G :=
  ⟨⊤, Subgroup.normal_top⟩

/-- Open normal subgroups form an order with top element the whole group. -/
instance instOrderTop : OrderTop (OpenNormalSubgroup G) where
  top := top
  le_top _ := SetLike.coe_subset_coe.mpr (Set.subset_univ _)

/-- The whole group is the canonical default open normal subgroup. -/
instance instInhabited : Inhabited (OpenNormalSubgroup G) :=
  ⟨⊤⟩

/-- Membership in the top open normal subgroup is automatic. -/
@[simp]
theorem mem_top (g : G) : g ∈ (⊤ : OpenNormalSubgroup G) := by
  change g ∈ (⊤ : Subgroup G)
  exact Subgroup.mem_top g

/-- The top open normal subgroup has the whole group as its underlying set. -/
@[simp, norm_cast]
theorem coe_top : ((⊤ : OpenNormalSubgroup G) : Set G) = Set.univ := by
  rfl

/-- The subgroup underlying the top open normal subgroup is the top subgroup. -/
@[simp, norm_cast]
theorem toSubgroup_top : ((⊤ : OpenNormalSubgroup G) : Subgroup G) = ⊤ := by
  rfl

end OpenNormalSubgroup

namespace OpenNormalAddSubgroup

variable {G : Type u} [AddGroup G] [TopologicalSpace G]

/-- The whole additive group as an open normal additive subgroup. -/
@[stacks 0BR1 "whole open normal additive subgroup"]
def top : OpenNormalAddSubgroup G :=
  ⟨⊤, AddSubgroup.normal_top⟩

/-- Open normal additive subgroups form an order with top element the whole additive group. -/
instance instOrderTop : OrderTop (OpenNormalAddSubgroup G) where
  top := top
  le_top _ := SetLike.coe_subset_coe.mpr (Set.subset_univ _)

/-- The whole additive group is the canonical default open normal additive subgroup. -/
instance instInhabited : Inhabited (OpenNormalAddSubgroup G) :=
  ⟨⊤⟩

/-- Membership in the top open normal additive subgroup is automatic. -/
@[simp]
theorem mem_top (g : G) : g ∈ (⊤ : OpenNormalAddSubgroup G) := by
  change g ∈ (⊤ : AddSubgroup G)
  exact AddSubgroup.mem_top g

/-- The top open normal additive subgroup has the whole additive group as its underlying set. -/
@[simp, norm_cast]
theorem coe_top : ((⊤ : OpenNormalAddSubgroup G) : Set G) = Set.univ := by
  rfl

/-- The additive subgroup underlying the top open normal additive subgroup is the top additive
subgroup. -/
@[simp, norm_cast]
theorem toAddSubgroup_top : ((⊤ : OpenNormalAddSubgroup G) : AddSubgroup G) = ⊤ := by
  rfl

end OpenNormalAddSubgroup

attribute [to_additive existing] OpenNormalSubgroup.top OpenNormalSubgroup.instOrderTop
  OpenNormalSubgroup.instInhabited OpenNormalSubgroup.mem_top OpenNormalSubgroup.coe_top
  OpenNormalSubgroup.toSubgroup_top
