/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Functoriality.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Computations

/-!
# One-cell computations for typed set-fibred inertia

This leaf records the based-functor, total-category, object, arrow, identity,
and composition readouts of the direct typed inertia map.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Sets.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C}

namespace map

/-- The based functor underlying a typed set-fibred inertia map is the neutral based map. -/
@[simp]
theorem toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toBasedFunctor (map F) =
      BasedCategory.Inertia.map
        (FiberedCategoryOver.Sets.toBasedFunctor F) := sorry

/-- The total functor underlying a typed set-fibred inertia map is the neutral total map. -/
@[simp]
theorem toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toFunctor (map F) =
      (BasedCategory.Inertia.map
        (FiberedCategoryOver.Sets.toBasedFunctor F)).toFunctor := sorry

/-- A typed set-fibred inertia map applies the source morphism to the underlying object. -/
@[simp]
theorem obj (F : X ⟶ Y) (A : X.inertia.total) :
    ((FiberedCategoryOver.Sets.toFunctor (map F)).obj A).obj =
      (FiberedCategoryOver.Sets.toFunctor F).obj A.obj := sorry

/-- A typed set-fibred inertia map applies the source morphism to the selected automorphism. -/
@[simp]
theorem aut (F : X ⟶ Y) (A : X.inertia.total) :
    ((FiberedCategoryOver.Sets.toFunctor (map F)).obj A).aut =
      (FiberedCategoryOver.Sets.toFunctor F).mapIso A.aut := sorry

/-- A typed set-fibred inertia map applies the source morphism to an underlying arrow. -/
@[simp]
theorem hom (F : X ⟶ Y) {A B : X.inertia.total} (f : A ⟶ B) :
    RelativeInertia.hom
        ((FiberedCategoryOver.Sets.toFunctor (map F)).map f) =
      (FiberedCategoryOver.Sets.toFunctor F).map (RelativeInertia.hom f) := sorry

/-- Typed set-fibred inertia preserves identity `1`-morphisms. -/
@[simp]
theorem id (X : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    map (𝟙 X) = 𝟙 (inertia X) := sorry

/-- Typed set-fibred inertia preserves composition of `1`-morphisms. -/
@[simp]
theorem comp {Z : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    map (F ≫ G) = map F ≫ map G := sorry

end map

end FiberedCategoryOver.Sets.Inertia

end CategoryTheory
