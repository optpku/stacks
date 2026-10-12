/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsoluteTransformations.Maps.Construction
@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
open scoped Bicategory
namespace FiberedCategoryOver.Sets.Inertia
variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
namespace forget
/-- The underlying based functor of set-fibred inertia forgetting. -/
@[simp]
theorem toBasedFunctor
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Sets.toBasedFunctor (forget X) =
      BasedCategory.Inertia.forget X.toBasedCategory := sorry
/-- The total functor of set-fibred inertia forgetting. -/
@[simp]
theorem toFunctor
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Sets.toFunctor (forget X) =
      RelativeInertia.forget X.toBasedCategory.toBase.toFunctor := sorry
/-- Forgetting an object returns its underlying object. -/
@[simp]
theorem obj
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C)
    (A : (FiberedCategoryOver.Sets.inertia X).total) :
    (FiberedCategoryOver.Sets.toFunctor (forget X)).obj A = A.obj := sorry
/-- Forgetting a morphism returns its underlying arrow. -/
@[simp]
theorem map
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C)
    {A B : (FiberedCategoryOver.Sets.inertia X).total} (φ : A ⟶ B) :
    (FiberedCategoryOver.Sets.toFunctor (forget X)).map φ =
      RelativeInertia.hom φ := sorry
end forget
namespace identitySection
/-- The underlying based functor of the identity section. -/
@[simp]
theorem toBasedFunctor
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Sets.toBasedFunctor (identitySection X) =
      BasedCategory.Inertia.identitySection X.toBasedCategory := sorry
/-- The total functor of the identity section. -/
@[simp]
theorem toFunctor
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Sets.toFunctor (identitySection X) =
      RelativeInertia.identitySection X.toBasedCategory.toBase.toFunctor := sorry
/-- The identity section preserves underlying objects. -/
@[simp]
theorem obj
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) (x : X.total) :
    ((FiberedCategoryOver.Sets.toFunctor (identitySection X)).obj x).obj = x := sorry
/-- The identity section selects the identity automorphism. -/
@[simp]
theorem aut
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) (x : X.total) :
    ((FiberedCategoryOver.Sets.toFunctor (identitySection X)).obj x).aut = 1 := sorry
/-- The identity section retains arrows. -/
@[simp]
theorem hom
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C)
    {x y : X.total} (f : x ⟶ y) :
    RelativeInertia.hom ((FiberedCategoryOver.Sets.toFunctor (identitySection X)).map f) = f := sorry
/-- The identity section is a right inverse to forgetting. -/
@[simp]
theorem comp_forget
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    identitySection X ≫ forget X = 𝟙 X := sorry
end identitySection
/-- Strictly discrete fibres make forgetting also a left inverse. -/
@[simp]
theorem forget.comp_identitySection
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    forget X ≫ identitySection X = 𝟙 (FiberedCategoryOver.Sets.inertia X) := sorry
/-- The forward equivalence morphism is forgetting. -/
@[simp]
theorem forget.equivalence.hom
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    (forget.equivalence X).hom = forget X := sorry
/-- The inverse equivalence morphism is the identity section. -/
@[simp]
theorem forget.equivalence.inv
    (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    (forget.equivalence X).inv = identitySection X := sorry
end FiberedCategoryOver.Sets.Inertia
end CategoryTheory
