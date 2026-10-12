/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsoluteTransformations.Maps.Construction
@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Setoids
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
namespace Inertia
variable {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
/-- The underlying based functor of setoid-fibred inertia forgetting. -/
@[simp]
theorem forget.toBasedFunctor
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Setoids.toBasedFunctor (forget X) =
      BasedCategory.Inertia.forget X.toBasedCategory := sorry

/-- The total functor of setoid-fibred inertia forgetting. -/
@[simp]
theorem forget.toFunctor
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Setoids.toFunctor (forget X) =
      CategoryTheory.RelativeInertia.forget X.toBasedCategory.toBase.toFunctor := sorry

/-- Forgetting an object returns its underlying object. -/
@[simp]
theorem forget.obj
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C)
    (A : (FiberedCategoryOver.Setoids.inertia X).total) :
    (FiberedCategoryOver.Setoids.toFunctor (forget X)).obj A = A.obj := sorry

/-- Forgetting a morphism returns its underlying arrow. -/
@[simp]
theorem forget.map
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C)
    {A B : (FiberedCategoryOver.Setoids.inertia X).total} (φ : A ⟶ B) :
    (FiberedCategoryOver.Setoids.toFunctor (forget X)).map φ =
      CategoryTheory.RelativeInertia.hom φ := sorry

/-- The underlying based functor of the identity section. -/
@[simp]
theorem identitySection.toBasedFunctor
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Setoids.toBasedFunctor (identitySection X) =
      BasedCategory.Inertia.identitySection X.toBasedCategory := sorry

/-- The total functor of the identity section. -/
@[simp]
theorem identitySection.toFunctor
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Setoids.toFunctor (identitySection X) =
      CategoryTheory.RelativeInertia.identitySection X.toBasedCategory.toBase.toFunctor := sorry

/-- The identity section preserves underlying objects. -/
@[simp]
theorem identitySection.obj
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) (x : X.total) :
    ((FiberedCategoryOver.Setoids.toFunctor (identitySection X)).obj x).obj = x := sorry

/-- The identity section selects the identity automorphism. -/
@[simp]
theorem identitySection.aut
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) (x : X.total) :
    ((FiberedCategoryOver.Setoids.toFunctor (identitySection X)).obj x).aut = 1 := sorry

/-- The identity section retains arrows. -/
@[simp]
theorem identitySection.hom
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C)
    {x y : X.total} (f : x ⟶ y) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toFunctor (identitySection X)).map f) = f := sorry

/-- The identity section is a right inverse to forgetting. -/
@[simp]
theorem identitySection.comp_forget
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    identitySection X ≫ forget X = 𝟙 X := sorry

/-- Thin fibres make the identity section also a left inverse. -/
@[simp]
theorem forget.comp_identitySection
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    forget X ≫ identitySection X = 𝟙 (FiberedCategoryOver.Setoids.inertia X) := sorry

/-- The forward equivalence morphism is forgetting. -/
@[simp]
theorem forget.equivalence.hom
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    (forget.equivalence X).hom = forget X := sorry

/-- The inverse equivalence morphism is the identity section. -/
@[simp]
theorem forget.equivalence.inv
    (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    (forget.equivalence X).inv = identitySection X := sorry
end Inertia
end FiberedCategoryOver.Setoids
end CategoryTheory
