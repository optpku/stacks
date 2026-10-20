module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.RelativeFunctoriality.Stable.Construction
import Mathlib.Tactic.CrossRefAttribute

/-! Stable-universe setoid-fibred relative inertia computations. -/
@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Setoids
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
namespace RelativeInertia
variable {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}

/-- The underlying based functor of setoid-fibred relative-inertia forgetting is the neutral
based forgetful map. -/
@[simp]
theorem forget.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toBasedFunctor (forget F) =
      BasedCategory.RelativeInertia.forget
        (FiberedCategoryOver.Setoids.toBasedFunctor F) := sorry


/-- The total functor of setoid-fibred relative-inertia forgetting is the neutral forgetful
functor. -/
@[simp]
theorem forget.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toFunctor (forget F) =
      CategoryTheory.RelativeInertia.forget
        (FiberedCategoryOver.Setoids.toFunctor F) := sorry



/-- The underlying based functor of the setoid-fibred relative identity section is the neutral
based section. -/
@[simp]
theorem identitySection.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toBasedFunctor (identitySection F) =
      BasedCategory.RelativeInertia.identitySection
        (FiberedCategoryOver.Setoids.toBasedFunctor F) := sorry


/-- The total functor of the setoid-fibred relative identity section is the neutral section. -/
@[simp]
theorem identitySection.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toFunctor (identitySection F) =
      CategoryTheory.RelativeInertia.identitySection
        (FiberedCategoryOver.Setoids.toFunctor F) := sorry




/-- Forgetting a setoid-fibred relative-inertia object returns its underlying source object. -/
@[simp]
theorem forget.obj
    (F : X ⟶ Y)
    (A : (FiberedCategoryOver.Setoids.relativeInertia F).total) :
    (FiberedCategoryOver.Setoids.toFunctor (forget F)).obj A = A.obj := sorry

/-- Forgetting a setoid-fibred relative-inertia morphism returns its underlying source arrow. -/
@[simp]
theorem forget.map
    (F : X ⟶ Y)
    {A B : (FiberedCategoryOver.Setoids.relativeInertia F).total}
    (φ : A ⟶ B) :
    (FiberedCategoryOver.Setoids.toFunctor (forget F)).map φ =
      CategoryTheory.RelativeInertia.hom φ := sorry

/-- The setoid-fibred relative identity section preserves the underlying object. -/
@[simp]
theorem identitySection.obj (F : X ⟶ Y) (x : X.total) :
    ((FiberedCategoryOver.Setoids.toFunctor (identitySection F)).obj x).obj = x := sorry

/-- The setoid-fibred relative identity section selects the identity automorphism. -/
@[simp]
theorem identitySection.aut (F : X ⟶ Y) (x : X.total) :
    ((FiberedCategoryOver.Setoids.toFunctor (identitySection F)).obj x).aut = 1 := sorry

/-- The arrow underlying the image of a morphism under the relative identity section is the
original arrow. -/
@[simp]
theorem identitySection.hom
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toFunctor (identitySection F)).map f) =
      f := sorry

/-- The relative identity section is a right inverse to relative-inertia forgetting. -/
@[simp]
theorem identitySection.comp_forget (F : X ⟶ Y) :
    identitySection F ≫ forget F = 𝟙 X := sorry

/-- Thin source fibres make the relative identity section also a left inverse to
relative-inertia forgetting. -/
@[simp]
theorem forget.comp_identitySection (F : X ⟶ Y) :
    forget F ≫ identitySection F =
      𝟙 (FiberedCategoryOver.Setoids.relativeInertia F) := sorry



/-- The forward morphism of the setoid relative-inertia equivalence forgets the selected
automorphism. -/
@[simp]
theorem forget.equivalence.hom (F : X ⟶ Y) :
    (forget.equivalence F).hom = forget F := sorry


/-- The inverse morphism of the setoid relative-inertia equivalence is the identity section. -/
@[simp]
theorem forget.equivalence.inv (F : X ⟶ Y) :
    (forget.equivalence F).inv = identitySection F := sorry


end RelativeInertia
end FiberedCategoryOver.Setoids
end CategoryTheory



