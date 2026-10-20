module

public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Factoring a functor through its induced category

Every functor `F : A ⥤ B` factors canonically through the category induced on
its object map.  The first factor retains the objects of `A` and regards every
mapped morphism as a morphism in `InducedCategory B F.obj`.
-/

@[expose] public section

universe vA vB uA uB

namespace CategoryTheory

namespace Functor

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The morphism assignment into the induced category preserves identities. -/
private theorem toInducedMap_id (F : A ⥤ B) (X : A) :
    InducedCategory.homMk (F := F.obj) (F.map (𝟙 X)) =
      InducedCategory.homMk (F := F.obj) (𝟙 (F.obj X)) := sorry

/-- The morphism assignment into the induced category preserves composition. -/
private theorem toInducedMap_comp
    (F : A ⥤ B) {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    InducedCategory.homMk (F := F.obj) (F.map (f ≫ g)) =
      InducedCategory.homMk (F := F.obj) (F.map f) ≫
        InducedCategory.homMk (F := F.obj) (F.map g) := sorry

/-- The canonical factor of a functor through the category induced by its
object map. -/
def toInduced (F : A ⥤ B) : A ⥤ InducedCategory B F.obj where
  obj X := X
  map f := InducedCategory.homMk (F := F.obj) (F.map f)
  map_id X := toInducedMap_id F X
  map_comp f g := toInducedMap_comp F f g

/-- The canonical factor through the induced category is the identity on
objects. -/
@[simp, stacks 02ZN]
theorem toInduced_obj (F : A ⥤ B) (X : A) :
    (toInduced F).obj X = X := sorry

/-- The canonical factor maps a morphism by packaging its image in the
induced category. -/
@[simp, stacks 02ZN]
theorem toInduced_map (F : A ⥤ B) {X Y : A} (f : X ⟶ Y) :
    (toInduced F).map f =
      InducedCategory.homMk (F := F.obj) (F.map f) := sorry

/-- Forgetting an induced morphism produced by `toInduced` recovers the
original mapped morphism. -/
@[simp, stacks 02ZN]
theorem toInduced_map_hom (F : A ⥤ B) {X Y : A} (f : X ⟶ Y) :
    ((toInduced F).map f).hom = F.map f := sorry

/-- Composing the canonical factor with the fully faithful induced functor
recovers the original functor. -/
@[simp, stacks 02ZN]
theorem toInduced_comp_inducedFunctor (F : A ⥤ B) :
    toInduced F ⋙ inducedFunctor F.obj = F := sorry

end Functor

end CategoryTheory
