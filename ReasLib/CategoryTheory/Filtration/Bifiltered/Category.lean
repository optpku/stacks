/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Bifiltered.Morphism
public import ReasLib.CategoryTheory.Filtration.Category

@[expose] public section

/-!
# The category of bifiltered objects

Bifiltered objects form a category. Forgetting either filtration is functorial, and both
filtered views have the same underlying morphism.
-/

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.BifilteredObject

variable {C : Type u} [Category.{v} C]

/-- The category of bifiltered objects and morphisms preserving both filtrations. -/
instance : Category (BifilteredObject C) where
  Hom X Y := Hom X Y
  id X := Hom.id X
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The underlying morphism of an identity bifiltered morphism is the identity. -/
@[simp]
theorem id_hom (X : BifilteredObject C) : (𝟙 X : X ⟶ X).hom = 𝟙 X.obj := sorry

/-- The underlying morphism of a composite is the composite of the underlying morphisms. -/
@[simp]
theorem comp_hom {X Y Z : BifilteredObject C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := sorry

/-- Forget the second filtration of a bifiltered object. -/
@[stacks 0ESK "first filtration functor"]
def first : BifilteredObject C ⥤ FilteredObject C where
  obj X := X.firstObj
  map f := f.first
  map_id := sorry
  map_comp := sorry

/-- Forget the first filtration of a bifiltered object. -/
@[stacks 0ESK "second filtration functor"]
def second : BifilteredObject C ⥤ FilteredObject C where
  obj X := X.secondObj
  map f := f.second
  map_id := sorry
  map_comp := sorry

/-- Forget both filtrations of a bifiltered object. -/
def forget : BifilteredObject C ⥤ C where
  obj X := X.obj
  map f := f.hom
  map_id := sorry
  map_comp := sorry

/-- Exchange the two filtrations functorially. -/
def swap : BifilteredObject C ⥤ BifilteredObject C where
  obj X := X.swapObj
  map f := f.swap
  map_id := sorry
  map_comp := sorry

/-- Forgetting the first filtered view gives the common underlying functor. -/
theorem first_comp_forget :
    first (C := C) ⋙ FilteredObject.forget = forget := sorry

/-- Forgetting the second filtered view gives the common underlying functor. -/
theorem second_comp_forget :
    second (C := C) ⋙ FilteredObject.forget = forget := sorry

end CategoryTheory.BifilteredObject
