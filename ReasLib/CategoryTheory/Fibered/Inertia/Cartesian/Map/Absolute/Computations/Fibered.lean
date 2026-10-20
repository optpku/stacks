/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Construction

/-!
# Computations for fixed fibred cartesian absolute-inertia maps

This leaf records based, heterogeneous, total, object, automorphism, and arrow projections for
the fixed fibred cartesian map owner.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia.map

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- Forgetting the bundled fibred structure from an inertia map recovers the canonical based map. -/
@[simp, stacks 04Z4 "fixed absolute-inertia based-functor computation"]
theorem toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor (map F) =
      BasedCategory.Inertia.map (FiberedCategoryOver.toBasedFunctor F) := sorry

/-- Forgetting a bundled inertia map to a cartesian based functor recovers the heterogeneous
absolute-inertia map. -/
@[simp, stacks 04Z4 "underlying cartesian absolute-inertia map"]
theorem toCartesianBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toCartesianBasedFunctor (map F) =
      CartesianBasedFunctor.Inertia.map
        (FiberedCategoryOver.toCartesianBasedFunctor F) := sorry

/-- The underlying total functor of a bundled absolute-inertia map is the canonical neutral
absolute-inertia map on total categories. -/
@[simp, stacks 04Z4 "fixed absolute-inertia total-functor computation"]
theorem toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor (map F) =
      (BasedCategory.Inertia.map
        (FiberedCategoryOver.toBasedFunctor F)).toFunctor := sorry

/-- A bundled inertia map applies the original total functor to the underlying object. -/
@[simp, stacks 04Z4 "fixed absolute-inertia object computation"]
theorem obj (F : X ⟶ Y)
    (A : (FiberedCategoryOver.inertia X).total) :
    ((FiberedCategoryOver.toFunctor (map F)).obj A).obj =
      (FiberedCategoryOver.toFunctor F).obj A.obj := sorry

/-- A bundled inertia map applies the original total functor to the chosen automorphism. -/
@[simp, stacks 04Z4 "fixed absolute-inertia automorphism computation"]
theorem aut (F : X ⟶ Y)
    (A : (FiberedCategoryOver.inertia X).total) :
    ((FiberedCategoryOver.toFunctor (map F)).obj A).aut =
      (FiberedCategoryOver.toFunctor F).mapIso A.aut := sorry

/-- A bundled inertia map applies the original total functor to the underlying arrow. -/
@[simp, stacks 04Z4 "fixed absolute-inertia arrow computation"]
theorem hom (F : X ⟶ Y)
    {A B : (FiberedCategoryOver.inertia X).total} (φ : A ⟶ B) :
    RelativeInertia.hom ((FiberedCategoryOver.toFunctor (map F)).map φ) =
      (FiberedCategoryOver.toFunctor F).map (RelativeInertia.hom φ) := sorry

/-- The bundled inertia map of an identity morphism is the identity. -/
@[simp, stacks 04Z4 "fixed absolute-inertia identity computation"]
theorem id (X : FiberedCategoryOver.{u, v, w, vS} C) :
    map (𝟙 X) = 𝟙 (FiberedCategoryOver.inertia X) := sorry

/-- The bundled inertia map preserves composition. -/
@[simp, stacks 04Z4 "fixed absolute-inertia composition computation"]
theorem comp
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    map (F ≫ G) = map F ≫ map G := sorry

end FiberedCategoryOver.Inertia.map

end CategoryTheory
