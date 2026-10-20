module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected

@[expose] public section

universe u

/-- A pro-`p` group is a compact Hausdorff totally disconnected topological group
whose quotients by open normal subgroups are `p`-groups. -/
def IsProPGroup (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  IsTopologicalGroup G ∧ CompactSpace G ∧ T2Space G ∧ TotallyDisconnectedSpace G ∧
    ∀ N : OpenNormalSubgroup G, IsPGroup p (G ⧸ N.toSubgroup)

namespace IsProPGroup

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G]

/-- Being pro-`p` is equivalent to profiniteness and having `p`-group quotients
by every open normal subgroup. -/
theorem iff :
    IsProPGroup p G ↔
      IsTopologicalGroup G ∧ CompactSpace G ∧ T2Space G ∧ TotallyDisconnectedSpace G ∧
        ∀ N : OpenNormalSubgroup G, IsPGroup p (G ⧸ N.toSubgroup) := Iff.rfl

/-- Every quotient of a pro-`p` group by an open normal subgroup is a `p`-group. -/
theorem isPGroup_quotient (hG : IsProPGroup p G) (N : OpenNormalSubgroup G) :
    IsPGroup p (G ⧸ N.toSubgroup) := hG.2.2.2.2 N

end IsProPGroup

/-- A maximal pro-`p` subgroup is a closed pro-`p` subgroup maximal among
closed pro-`p` subgroups. -/
def IsMaximalProPSubgroup (p : ℕ) {G : Type u} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : Prop :=
  IsProPGroup p H ∧ IsClosed (H : Set G) ∧
    ∀ K : Subgroup G, IsProPGroup p K → IsClosed (K : Set G) → H ≤ K → K = H

namespace IsMaximalProPSubgroup

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] {H : Subgroup G}

/-- A maximal pro-`p` subgroup is a pro-`p` group. -/
theorem isProPGroup (hH : IsMaximalProPSubgroup p H) : IsProPGroup p H := hH.1

/-- A maximal pro-`p` subgroup is closed. -/
theorem isClosed (hH : IsMaximalProPSubgroup p H) : IsClosed (H : Set G) := hH.2.1

/-- A closed pro-`p` supergroup of a maximal pro-`p` subgroup equals it. -/
theorem eq_of_le (hH : IsMaximalProPSubgroup p H) {K : Subgroup G}
    (hK : IsProPGroup p K) (hKcl : IsClosed (K : Set G)) (hHK : H ≤ K) : K = H :=
  hH.2.2 K hK hKcl hHK

/-- Maximal pro-`p` subgroups are precisely the closed pro-`p` subgroups that
have no strictly larger closed pro-`p` supergroup. -/
theorem iff :
    IsMaximalProPSubgroup p H ↔
      IsProPGroup p H ∧ IsClosed (H : Set G) ∧
        ∀ K : Subgroup G, IsProPGroup p K → IsClosed (K : Set G) → H ≤ K → K = H :=
  Iff.rfl

end IsMaximalProPSubgroup
