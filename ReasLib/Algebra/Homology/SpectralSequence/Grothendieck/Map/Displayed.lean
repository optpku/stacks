/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map.Category
public import ReasLib.CategoryTheory.DisplayedCategory.Transport

/-!
# Displayed category of Grothendieck spectral-sequence realizations

This leaf presents the existing Grothendieck spectral-sequence map API as a displayed category
over the derived category.  The owner `SpectralSequence.Map.reindex` remains the canonical
transport along an equality of base arrows; the final bridge theorem records its agreement with
the generic displayed-category transport.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C] [HasInjectiveResolutions B]
variable {G : B ⥤ C} [G.Additive]
variable {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
variable {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}

/-- The displayed category of Grothendieck spectral-sequence realizations over the derived
category.  Its displayed objects are chosen realizations and its displayed morphisms are the
existing `SpectralSequence.Map` data. -/
@[stacks 015N "displayed category of Grothendieck spectral sequences"]
noncomputable def displayedCategory
    (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) :
    DisplayedCategory (DerivedCategory.Plus A) where
  obj X := SpectralSequence G RF RGF X
  Hom := fun {X Y} f S T => Map f S T
  id := fun {X} S => Map.id S
  comp := fun {X Y Z} {f g} {S T U} m n => Map.comp m n
  id_comp := fun _ => sorry
  comp_id := fun _ => sorry
  assoc := fun _ _ _ => sorry

/-- The displayed-object family of `displayedCategory` is the chosen spectral-sequence family. -/
@[simp, stacks 015N "displayed Grothendieck spectral-sequence objects"]
theorem displayedCategory_obj
    (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    (X : DerivedCategory.Plus A) :
    (displayedCategory G RF RGF).obj X = SpectralSequence G RF RGF X := sorry

/-- The displayed hom family of `displayedCategory` is the existing spectral-sequence map family. -/
@[simp, stacks 015N "displayed Grothendieck spectral-sequence maps"]
theorem displayedCategory_hom
    (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    (S : SpectralSequence G RF RGF X) (T : SpectralSequence G RF RGF Y) :
    (displayedCategory G RF RGF).Hom f S T = Map f S T := sorry

/-- The identity operation of `displayedCategory` is `SpectralSequence.Map.id`. -/
@[simp, stacks 015N "displayed Grothendieck spectral-sequence identity"]
theorem displayedCategory_id
    (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    {X : DerivedCategory.Plus A} (S : SpectralSequence G RF RGF X) :
    (displayedCategory G RF RGF).id S = Map.id S := sorry

/-- The composition operation of `displayedCategory` is `SpectralSequence.Map.comp`. -/
@[simp, stacks 015N "displayed Grothendieck spectral-sequence composition"]
theorem displayedCategory_comp
    (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    {X Y Z : DerivedCategory.Plus A} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    {U : SpectralSequence G RF RGF Z}
    (m : Map f S T) (n : Map g T U) :
    (displayedCategory G RF RGF).comp m n = Map.comp m n := sorry

/-- The owner-level base reindexing of a spectral-sequence map agrees with generic displayed
transport for `displayedCategory`. -/
@[simp, stacks 015N "displayed Grothendieck spectral-sequence transport"]
theorem Map.reindex_eq_cast {X Y : DerivedCategory.Plus A} {f g : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (h : f = g) (m : Map f S T) :
    Map.reindex h m = DisplayedCategory.Hom.cast (displayedCategory G RF RGF) h m := sorry

/-- The generic displayed transport can be converted back to the owner-level Grothendieck map
reindexing. -/
@[stacks 015N "owner-level transport of Grothendieck spectral-sequence maps"]
theorem Map.cast_eq_reindex {X Y : DerivedCategory.Plus A} {f g : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (h : f = g) (m : Map f S T) :
    DisplayedCategory.Hom.cast (displayedCategory G RF RGF) h m = Map.reindex h m :=
  (Map.reindex_eq_cast h m).symm

end CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence

end
