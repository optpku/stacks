/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.RelativeFunctoriality.Stable.Construction
import Mathlib.Tactic.CrossRefAttribute

/-! Stable-universe set-fibred relative inertia computations. -/

@[expose] public section

universe u v vS w

namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Sets
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
namespace RelativeInertia
variable {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}

/-- The based functor underlying relative-inertia forgetting is the neutral forgetful map. -/
@[simp]
theorem forget.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toBasedFunctor (forget F) =
      BasedCategory.RelativeInertia.forget
        (FiberedCategoryOver.Sets.toBasedFunctor F) := sorry

/-- The total functor underlying relative-inertia forgetting is neutral. -/
@[simp]
theorem forget.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toFunctor (forget F) =
      CategoryTheory.RelativeInertia.forget
        (FiberedCategoryOver.Sets.toFunctor F) := sorry

/-- The based functor underlying the relative identity section is the neutral section. -/
@[simp]
theorem identitySection.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toBasedFunctor (identitySection F) =
      BasedCategory.RelativeInertia.identitySection
        (FiberedCategoryOver.Sets.toBasedFunctor F) := sorry

/-- The total functor underlying the relative identity section is the neutral section. -/
@[simp]
theorem identitySection.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toFunctor (identitySection F) =
      CategoryTheory.RelativeInertia.identitySection
        (FiberedCategoryOver.Sets.toFunctor F) := sorry

/-- Forgetting a set-fibred relative-inertia object returns its underlying source object. -/
@[simp]
theorem forget.obj
    (F : X ⟶ Y)
    (A : (FiberedCategoryOver.Sets.relativeInertia F).total) :
    (FiberedCategoryOver.Sets.toFunctor (forget F)).obj A = A.obj := sorry

/-- Forgetting a set-fibred relative-inertia morphism returns its underlying source arrow. -/
@[simp]
theorem forget.map
    (F : X ⟶ Y)
    {A B : (FiberedCategoryOver.Sets.relativeInertia F).total}
    (φ : A ⟶ B) :
    (FiberedCategoryOver.Sets.toFunctor (forget F)).map φ =
      CategoryTheory.RelativeInertia.hom φ := sorry

/-- The set-fibred relative identity section preserves the underlying object. -/
@[simp]
theorem identitySection.obj (F : X ⟶ Y) (x : X.total) :
    ((FiberedCategoryOver.Sets.toFunctor (identitySection F)).obj x).obj = x := sorry

/-- The set-fibred relative identity section selects the identity automorphism. -/
@[simp]
theorem identitySection.aut (F : X ⟶ Y) (x : X.total) :
    ((FiberedCategoryOver.Sets.toFunctor (identitySection F)).obj x).aut = 1 := sorry

/-- The arrow underlying the image of a morphism under the relative identity section is the
original arrow. -/
@[simp]
theorem identitySection.hom
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Sets.toFunctor (identitySection F)).map f) =
      f := sorry

/-- The forward morphism of the relative-inertia equivalence is forgetting. -/
@[simp]
theorem forget.equivalence.hom (F : X ⟶ Y) :
    (forget.equivalence F).hom = forget F := sorry

/-- The inverse morphism of the relative-inertia equivalence is the identity section. -/
@[simp]
theorem forget.equivalence.inv (F : X ⟶ Y) :
    (forget.equivalence F).inv = identitySection F := sorry

/-- The relative identity section is a right inverse to forgetting. -/
@[simp]
theorem identitySection.comp_forget (F : X ⟶ Y) :
    identitySection F ≫ forget F = 𝟙 X := sorry

/-- Strictly discrete fibres make relative-inertia forgetting a left inverse to the identity
section. -/
@[simp]
theorem forget.comp_identitySection (F : X ⟶ Y) :
    forget F ≫ identitySection F =
      𝟙 (FiberedCategoryOver.Sets.relativeInertia F) := sorry

end RelativeInertia
end FiberedCategoryOver.Sets
end CategoryTheory
