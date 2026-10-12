/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Action.SmallBoundClosed

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

variable {G : Type u} [Group G]

#check (Action.IsSmallBoundClosed : ObjectProperty (Action (Type u) G) → Prop)
#check (Action.exists_iso_of_size_le_bound :
  ∀ {P : ObjectProperty (Action (Type u) G)}, Action.IsSmallBoundClosed P →
    ∀ {S T : Action (Type u) G}, P S → T.size ≤ Action.bound S.size →
      ∃ S' : Action (Type u) G, P S' ∧ Nonempty (T ≅ S'))
#check (Action.sizeLE_bound_le_isoClosure :
  ∀ {P : ObjectProperty (Action (Type u) G)}, Action.IsSmallBoundClosed P →
    ∀ {S : Action (Type u) G}, P S → Action.sizeLE (Action.bound S.size) ≤ P.isoClosure)
#check (Action.hasLimit :
  ∀ {P : ObjectProperty (Action (Type u) G)}, Action.IsSmallBoundClosed P →
    ∀ {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory),
      HasLimit F)
#check (Action.isIso_limit_post :
  ∀ {P : ObjectProperty (Action (Type u) G)}, Action.IsSmallBoundClosed P →
    ∀ {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory)
      [HasLimit F] [HasLimit (F ⋙ P.ι)], IsIso (limit.post F P.ι))
#check (Action.hasColimit :
  ∀ {P : ObjectProperty (Action (Type u) G)}, Action.IsSmallBoundClosed P →
    ∀ {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory),
      HasColimit F)
#check (Action.isIso_colimit_post :
  ∀ {P : ObjectProperty (Action (Type u) G)}, Action.IsSmallBoundClosed P →
    ∀ {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory)
      [HasColimit F] [HasColimit (F ⋙ P.ι)], IsIso (colimit.post F P.ι))
