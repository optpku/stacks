/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps.Construction

/-! Groupoid-fibred inertia transformation readouts. -/
@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Groupoids
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
namespace Inertia
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}

/-- The underlying based functor of groupoid-fibred inertia forgetting. -/
@[simp]
theorem forget.toBasedFunctor
    (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (forget X) =
      BasedCategory.Inertia.forget X.toBasedCategory := sorry
/-- The total functor of groupoid-fibred inertia forgetting. -/
@[simp]
theorem forget.toFunctor
    (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Groupoids.toFunctor (forget X) =
      RelativeInertia.forget X.toBasedCategory.toBase.toFunctor := sorry
/-- Forgetting an object returns its underlying object. -/
@[simp]
theorem forget.obj
    (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C)
    (A : (FiberedCategoryOver.Groupoids.inertia X).total) :
    (FiberedCategoryOver.Groupoids.toFunctor (forget X)).obj A = A.obj := sorry
/-- Forgetting a morphism returns its underlying arrow. -/
@[simp]
theorem forget.map
    (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C)
    {A B : (FiberedCategoryOver.Groupoids.inertia X).total} (φ : A ⟶ B) :
    (FiberedCategoryOver.Groupoids.toFunctor (forget X)).map φ = RelativeInertia.hom φ := sorry

/-- The underlying based functor of the identity section. -/
@[simp]
theorem identitySection.toBasedFunctor
    (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (identitySection X) =
      BasedCategory.Inertia.identitySection X.toBasedCategory := sorry
/-- The total functor of the identity section. -/
@[simp]
theorem identitySection.toFunctor
    (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Groupoids.toFunctor (identitySection X) =
      RelativeInertia.identitySection X.toBasedCategory.toBase.toFunctor := sorry
/-- The identity section preserves underlying objects. -/
@[simp]
theorem identitySection.obj
    (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C) (x : X.total) :
    ((FiberedCategoryOver.Groupoids.toFunctor (identitySection X)).obj x).obj = x := sorry
/-- The identity section selects the identity automorphism. -/
@[simp]
theorem identitySection.aut
    (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C) (x : X.total) :
    ((FiberedCategoryOver.Groupoids.toFunctor (identitySection X)).obj x).aut = 1 := sorry
/-- The identity section retains underlying arrows. -/
@[simp]
theorem identitySection.hom
    (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C)
    {x y : X.total} (f : x ⟶ y) :
    RelativeInertia.hom ((FiberedCategoryOver.Groupoids.toFunctor (identitySection X)).map f) = f := sorry
/-- The identity section is a right inverse to forgetting. -/
@[simp]
theorem identitySection.comp_forget
    (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C) :
    identitySection X ≫ forget X = 𝟙 X := sorry

end Inertia
end FiberedCategoryOver.Groupoids
end CategoryTheory
