module

public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped Cardinal

namespace Action

/-- The Stacks size of a `G`-set, `ℵ₀ ⊔ #G ⊔ #(S.V)`. -/
noncomputable def size {G : Type u} [Group G] (S : Action (Type u) G) : Cardinal.{u} :=
  ℵ₀ ⊔ #G ⊔ #(S.V)

/-- The Stacks Bound function on cardinals for `G`-sets, sending `κ` to `κ ^ ℵ₀`. -/
noncomputable def bound (κ : Cardinal.{u}) : Cardinal.{u} :=
  κ ^ ℵ₀

/-- Unfolding of `bound`. -/
theorem bound_eq (κ : Cardinal.{u}) : bound κ = κ ^ ℵ₀ := sorry

variable {G : Type u} [Group G]

/-- Unfolding of `size`. -/
theorem size_eq (S : Action (Type u) G) : size S = ℵ₀ ⊔ #G ⊔ #(S.V) := sorry

/-- Countable infinite cardinals are bounded by the Stacks size of any `G`-set. -/
theorem aleph0_le_size (S : Action (Type u) G) : ℵ₀ ≤ S.size := sorry

/-- The acting group is bounded in cardinality by the Stacks size of any `G`-set. -/
theorem mk_group_le_size (S : Action (Type u) G) : #G ≤ S.size := sorry

/-- The underlying set is bounded in cardinality by the Stacks size. -/
theorem mk_le_size (S : Action (Type u) G) : #(S.V) ≤ S.size := sorry

/-- Isomorphic `G`-sets have the same size. -/
theorem size_eq_of_iso {S T : Action (Type u) G} (e : S ≅ T) : size S = size T := sorry

/-- The object property of `G`-sets of size at most `κ`. -/
def sizeLE (κ : Cardinal.{u}) : ObjectProperty (Action (Type u) G) :=
  fun S ↦ S.size ≤ κ

/-- Membership in `sizeLE κ` is the inequality `size S ≤ κ`. -/
theorem sizeLE_iff (κ : Cardinal.{u}) (S : Action (Type u) G) :
    sizeLE κ S ↔ S.size ≤ κ := sorry

namespace sizeLE

/-- The property of having size at most `κ` is invariant under isomorphism of `G`-sets. -/
instance instIsClosedUnderIsomorphisms (κ : Cardinal.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (sizeLE κ : ObjectProperty (Action (Type u) G)) := sorry

end sizeLE

end Action
