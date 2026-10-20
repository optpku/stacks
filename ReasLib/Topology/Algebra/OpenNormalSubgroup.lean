module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open normal subgroups

Reusable order-theoretic structure on open normal subgroups of a topological group.
Mathlib already supplies finite intersections; this file records the canonical whole-group
element, which makes the indexing type nonempty without a local choice or instance pin, and
the pullback `OpenNormalSubgroup.comap` along continuous homomorphisms (mathlib only provides
`OpenSubgroup.comap`).
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

namespace OpenNormalSubgroup

universe v w

variable {G : Type v} {H : Type w} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- The preimage of an open normal subgroup along a continuous group homomorphism. -/
@[to_additive /-- The preimage of an open normal additive subgroup along a continuous additive
group homomorphism. -/]
def comap (f : G →* H) (hf : Continuous f) (N : OpenNormalSubgroup H) :
    OpenNormalSubgroup G where
  toOpenSubgroup := N.toOpenSubgroup.comap f hf
  isNormal' := N.isNormal'.comap f

/-- The underlying set of a pulled-back open normal subgroup is the preimage. -/
@[to_additive (attr := simp, norm_cast)]
theorem coe_comap (f : G →* H) (hf : Continuous f) (N : OpenNormalSubgroup H) :
    (N.comap f hf : Set G) = f ⁻¹' N :=
  rfl

/-- The underlying subgroup of a pulled-back open normal subgroup is the subgroup comap. -/
@[to_additive (attr := simp)]
theorem toSubgroup_comap (f : G →* H) (hf : Continuous f) (N : OpenNormalSubgroup H) :
    (N.comap f hf).toSubgroup = N.toSubgroup.comap f :=
  rfl

/-- Membership in a pulled-back open normal subgroup. -/
@[to_additive (attr := simp)]
theorem mem_comap {f : G →* H} {hf : Continuous f} {N : OpenNormalSubgroup H} {x : G} :
    x ∈ N.comap f hf ↔ f x ∈ N :=
  Iff.rfl

/-- Pullback of open normal subgroups is monotone. -/
@[to_additive]
theorem comap_mono {N N' : OpenNormalSubgroup H} (f : G →* H) (hf : Continuous f)
    (h : N ≤ N') : N.comap f hf ≤ N'.comap f hf :=
  fun _ hx ↦ h hx

end OpenNormalSubgroup
