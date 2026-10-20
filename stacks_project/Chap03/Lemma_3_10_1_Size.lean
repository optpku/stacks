module

public import ReasLib.CategoryTheory.Action.Size

@[expose] public section

universe u

open CategoryTheory
open scoped Cardinal

variable {G : Type u} [Group G]

#check (Action.size : Action (Type u) G → Cardinal.{u})
#check (Action.bound : Cardinal.{u} → Cardinal.{u})
#check (Action.bound_eq : ∀ κ : Cardinal.{u}, Action.bound κ = κ ^ ℵ₀)
#check (Action.size_eq : ∀ S : Action (Type u) G, S.size = ℵ₀ ⊔ #G ⊔ #(S.V))
#check (Action.aleph0_le_size : ∀ S : Action (Type u) G, ℵ₀ ≤ S.size)
#check (Action.mk_group_le_size : ∀ S : Action (Type u) G, #G ≤ S.size)
#check (Action.mk_le_size : ∀ S : Action (Type u) G, #(S.V) ≤ S.size)
#check (Action.size_eq_of_iso : ∀ {S T : Action (Type u) G}, (S ≅ T) → S.size = T.size)
#check (Action.sizeLE : Cardinal.{u} → ObjectProperty (Action (Type u) G))
#check (Action.sizeLE_iff : ∀ (κ : Cardinal.{u}) (S : Action (Type u) G),
  Action.sizeLE κ S ↔ S.size ≤ κ)
#check (Action.sizeLE.instIsClosedUnderIsomorphisms : ∀ κ : Cardinal.{u},
  ObjectProperty.IsClosedUnderIsomorphisms
    (Action.sizeLE κ : ObjectProperty (Action (Type u) G)))
