/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Morphism

/-!
# Category of Filtered Objects

The filtered objects in `C` form a category with the filtration-preserving morphisms.
The forgetful functor to `C` is faithful.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FilteredObject

/-- The category structure on filtered objects with filtration-preserving morphisms. -/
@[reducible] def categoryStructure : Category (FilteredObject C) where
  Hom X Y := FilteredObject.Hom X Y
  id X := Hom.id X
  comp f g := Hom.comp f g
  id_comp := id_comp_eq
  comp_id := comp_id_eq
  assoc := assoc_eq

/-- The canonical category of filtered objects over `C`. -/
instance instCategory : Category (FilteredObject C) := categoryStructure

/-- The underlying morphism of a filtered identity is the ambient identity. -/
@[simp] theorem id_hom (X : FilteredObject C) : (𝟙 X : X ⟶ X).hom = 𝟙 X.obj := rfl

/-- The underlying morphism of a filtered composite is the composite of the underlying morphisms. -/
@[simp] theorem comp_hom {X Y Z : FilteredObject C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The forgetful functor from filtered objects to the ambient category. -/
def forget : FilteredObject C ⥤ C where
  obj X := X.obj
  map f := f.hom

/-- Evaluating the forgetful functor on a filtered object gives its underlying object. -/
@[simp]
theorem forget_obj (X : FilteredObject C) : forget.obj X = X.obj := sorry

/-- Evaluating the forgetful functor on a filtered morphism gives its underlying morphism. -/
@[simp]
theorem forget_map {X Y : FilteredObject C} (f : X ⟶ Y) : forget.map f = f.hom := sorry

/-- The forgetful functor from filtered objects is faithful. -/
@[instance] theorem forget_faithful : Functor.Faithful (forget (C := C)) :=
  { map_injective := fun {_ _} _ _ h => FilteredObject.Hom.ext h }

variable {X Y : FilteredObject C}

/-- A filtered morphism is an epimorphism if its underlying morphism is an epimorphism. -/
@[instance] theorem epi_of_epi_hom (f : X ⟶ Y) [Epi f.hom] : Epi f :=
  (forget : FilteredObject C ⥤ C).epi_of_epi_map (by simpa)

/-- A filtered morphism is a monomorphism if its underlying morphism is a monomorphism. -/
@[instance] theorem mono_of_mono_hom (f : X ⟶ Y) [Mono f.hom] : Mono f :=
  (forget : FilteredObject C ⥤ C).mono_of_mono_map (by simpa)

end FilteredObject

end CategoryTheory
