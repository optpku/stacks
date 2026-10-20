/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.GroupTheory.ProP

@[expose] public section

universe u

#check (IsProPGroup :
  ℕ → ∀ (G : Type u) [Group G] [TopologicalSpace G], Prop)

#check (IsProPGroup.iff :
  ∀ {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G],
    IsProPGroup p G ↔
      IsTopologicalGroup G ∧ CompactSpace G ∧ T2Space G ∧ TotallyDisconnectedSpace G ∧
        ∀ N : OpenNormalSubgroup G, IsPGroup p (G ⧸ N.toSubgroup))

#check (IsProPGroup.isPGroup_quotient :
  ∀ {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G],
    IsProPGroup p G → ∀ N : OpenNormalSubgroup G, IsPGroup p (G ⧸ N.toSubgroup))

#check (IsMaximalProPSubgroup :
  ℕ → ∀ {G : Type u} [Group G] [TopologicalSpace G], Subgroup G → Prop)

#check (IsMaximalProPSubgroup.isProPGroup :
  ∀ {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] {H : Subgroup G},
    IsMaximalProPSubgroup p H → IsProPGroup p H)

#check (IsMaximalProPSubgroup.isClosed :
  ∀ {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] {H : Subgroup G},
    IsMaximalProPSubgroup p H → IsClosed (H : Set G))

#check (IsMaximalProPSubgroup.eq_of_le :
  ∀ {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] {H : Subgroup G},
    IsMaximalProPSubgroup p H → ∀ {K : Subgroup G},
      IsProPGroup p K → IsClosed (K : Set G) → H ≤ K → K = H)

#check (IsMaximalProPSubgroup.iff :
  ∀ {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] {H : Subgroup G},
    IsMaximalProPSubgroup p H ↔
      IsProPGroup p H ∧ IsClosed (H : Set G) ∧
        ∀ K : Subgroup G, IsProPGroup p K → IsClosed (K : Set G) → H ≤ K → K = H)
