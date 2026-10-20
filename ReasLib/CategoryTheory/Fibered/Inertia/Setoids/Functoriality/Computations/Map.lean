module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Functoriality.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Computations

/-!
# One-cell computations for typed setoid-fibred inertia

This leaf records the based-functor, total-category, object, arrow, identity,
and composition readouts of the direct typed inertia map.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Setoids.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C}

namespace map

/-- The based functor underlying a typed inertia map is the neutral based map. -/
@[simp]
theorem toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toBasedFunctor (map F) =
      BasedCategory.Inertia.map
        (FiberedCategoryOver.Setoids.toBasedFunctor F) := sorry

/-- The total functor underlying a typed inertia map is the neutral total map. -/
@[simp]
theorem toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toFunctor (map F) =
      (BasedCategory.Inertia.map
        (FiberedCategoryOver.Setoids.toBasedFunctor F)).toFunctor := sorry

/-- A typed inertia map applies the source morphism to the underlying object. -/
@[simp]
theorem obj (F : X ⟶ Y) (A : X.inertia.total) :
    ((FiberedCategoryOver.Setoids.toFunctor (map F)).obj A).obj =
      (FiberedCategoryOver.Setoids.toFunctor F).obj A.obj := sorry

/-- A typed inertia map applies the source morphism to the selected automorphism. -/
@[simp]
theorem aut (F : X ⟶ Y) (A : X.inertia.total) :
    ((FiberedCategoryOver.Setoids.toFunctor (map F)).obj A).aut =
      (FiberedCategoryOver.Setoids.toFunctor F).mapIso A.aut := sorry

/-- A typed inertia map applies the source morphism to an underlying arrow. -/
@[simp]
theorem hom (F : X ⟶ Y) {A B : X.inertia.total} (f : A ⟶ B) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toFunctor (map F)).map f) =
      (FiberedCategoryOver.Setoids.toFunctor F).map (RelativeInertia.hom f) := sorry

/-- Typed inertia preserves identity `1`-morphisms. -/
@[simp]
theorem id (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    map (𝟙 X) = 𝟙 (inertia X) := sorry

/-- Typed inertia preserves composition of `1`-morphisms. -/
@[simp]
theorem comp {Z : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    map (F ≫ G) = map F ≫ map G := sorry

end map

end FiberedCategoryOver.Setoids.Inertia

end CategoryTheory
