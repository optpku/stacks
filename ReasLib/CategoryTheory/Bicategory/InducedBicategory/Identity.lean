module

public import Mathlib.CategoryTheory.Bicategory.InducedBicategory

/-!
# The identity embedding into an induced bicategory

This leaf supplies the canonical strict pseudofunctor from a bicategory to
the induced bicategory on its own object type and identity object map.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open scoped Bicategory

universe w v u

namespace Bicategory.InducedBicategory

/-- The canonical strict pseudofunctor from a bicategory to the induced
bicategory on its identity object map.

It wraps each ambient 1-morphism and 2-morphism in the induced-bicategory
representative, without changing its mathematical content. -/
def toInduced (C : Type u) [Bicategory.{w, v} C] :
    StrictPseudofunctor C (InducedBicategory C id) :=
  StrictPseudofunctor.mk' {
    obj := fun X ↦ X
    map := fun f ↦ mkHom f
    map₂ := fun η ↦ mkHom₂ η
    map₂_id := sorry
    map₂_comp := sorry
    map_id := sorry
    map_comp := sorry
    map₂_whisker_left := sorry
    map₂_whisker_right := sorry
    map₂_left_unitor := sorry
    map₂_right_unitor := sorry
    map₂_associator := sorry }

/-- The identity embedding retains each object. -/
@[simp]
theorem toInduced_obj (C : Type u) [Bicategory.{w, v} C] (X : C) :
    (toInduced C).obj X = X := sorry

/-- The identity embedding retains the ambient representative of each
1-morphism. -/
@[simp]
theorem toInduced_map_hom (C : Type u) [Bicategory.{w, v} C]
    {X Y : C} (f : X ⟶ Y) :
    ((toInduced C).map f).hom = f := sorry

/-- The identity embedding retains the ambient representative of each
2-morphism. -/
@[simp]
theorem toInduced_map₂_hom (C : Type u) [Bicategory.{w, v} C]
    {X Y : C} {f g : X ⟶ Y} (η : f ⟶ g) :
    ((toInduced C).map₂ η).hom = η := sorry

end Bicategory.InducedBicategory

end CategoryTheory
