module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Relative.Construction

/-!
# Computations for the cartesian relative-to-absolute comparison

This leaf exposes the based and total projections and the objectwise formulas for `toInertia`.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.toInertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- Forgetting the fibred structure from the relative-to-absolute comparison recovers the
canonical based comparison. -/
@[simp]
theorem toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor (toInertia F) =
      BasedCategory.RelativeInertia.toInertia
        (FiberedCategoryOver.toBasedFunctor F) := sorry

/-- The total functor of the fibred relative-to-absolute comparison is the neutral comparison. -/
@[simp]
theorem toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor (toInertia F) =
      (BasedCategory.RelativeInertia.toInertia
        (FiberedCategoryOver.toBasedFunctor F)).toFunctor := sorry

/-- The relative-to-absolute comparison retains the underlying source object. -/
@[simp]
theorem obj (F : X ⟶ Y) (A : (FiberedCategoryOver.relativeInertia F).total) :
    ((FiberedCategoryOver.toFunctor (toInertia F)).obj A).obj = A.obj := sorry

/-- The relative-to-absolute comparison retains the selected automorphism. -/
@[simp]
theorem aut (F : X ⟶ Y) (A : (FiberedCategoryOver.relativeInertia F).total) :
    ((FiberedCategoryOver.toFunctor (toInertia F)).obj A).aut = A.aut := sorry

/-- The relative-to-absolute comparison retains the arrow underlying every morphism. -/
@[simp]
theorem hom
    (F : X ⟶ Y) {A B : (FiberedCategoryOver.relativeInertia F).total} (φ : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toFunctor (toInertia F)).map φ) =
      CategoryTheory.RelativeInertia.hom φ := sorry

end FiberedCategoryOver.RelativeInertia.toInertia

end CategoryTheory
