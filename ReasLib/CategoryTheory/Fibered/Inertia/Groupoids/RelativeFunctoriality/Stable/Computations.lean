/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Stable.Construction
import Mathlib.Tactic.CrossRefAttribute

/-! Stable-universe groupoid-fibred relative inertia computations. -/
@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Groupoids
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
namespace RelativeInertia
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}

/-- The underlying based functor of groupoid-fibred relative-inertia forgetting is the neutral
based forgetful map. -/
@[simp]
theorem forget.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (forget F) =
      BasedCategory.RelativeInertia.forget
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) := sorry


/-- The total functor of groupoid-fibred relative-inertia forgetting is the neutral forgetful
functor. -/
@[simp]
theorem forget.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toFunctor (forget F) =
      CategoryTheory.RelativeInertia.forget
        (FiberedCategoryOver.Groupoids.toFunctor F) := sorry



/-- The underlying based functor of the groupoid-fibred relative identity section is the neutral
based section. -/
@[simp]
theorem identitySection.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (identitySection F) =
      BasedCategory.RelativeInertia.identitySection
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) := sorry


/-- The total functor of the groupoid-fibred relative identity section is the neutral
section. -/
@[simp]
theorem identitySection.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toFunctor (identitySection F) =
      CategoryTheory.RelativeInertia.identitySection
        (FiberedCategoryOver.Groupoids.toFunctor F) := sorry



/-- Forgetting a groupoid-fibred relative-inertia object returns its underlying source
object. -/
@[simp]
theorem forget.obj
    (F : X ⟶ Y)
    (A : (FiberedCategoryOver.Groupoids.relativeInertia F).total) :
    (FiberedCategoryOver.Groupoids.toFunctor (forget F)).obj A = A.obj := sorry

/-- Forgetting a groupoid-fibred relative-inertia morphism returns its underlying source
arrow. -/
@[simp]
theorem forget.map
    (F : X ⟶ Y)
    {A B : (FiberedCategoryOver.Groupoids.relativeInertia F).total}
    (φ : A ⟶ B) :
    (FiberedCategoryOver.Groupoids.toFunctor (forget F)).map φ =
      CategoryTheory.RelativeInertia.hom φ := sorry


/-- The groupoid-fibred relative identity section preserves the underlying object. -/
@[simp]
theorem identitySection.obj (F : X ⟶ Y) (x : X.total) :
    ((FiberedCategoryOver.Groupoids.toFunctor (identitySection F)).obj x).obj = x := sorry

/-- The groupoid-fibred relative identity section selects the identity automorphism. -/
@[simp]
theorem identitySection.aut (F : X ⟶ Y) (x : X.total) :
    ((FiberedCategoryOver.Groupoids.toFunctor (identitySection F)).obj x).aut = 1 := sorry

/-- The arrow underlying the image of a morphism under the relative identity section is the
original arrow. -/
@[simp]
theorem identitySection.hom
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toFunctor (identitySection F)).map f) =
      f := sorry

/-- The relative identity section is a right inverse to relative-inertia forgetting. -/
@[simp]
theorem identitySection.comp_forget (F : X ⟶ Y) :
    identitySection F ≫ forget F = 𝟙 X := sorry


end RelativeInertia
end FiberedCategoryOver.Groupoids
end CategoryTheory


