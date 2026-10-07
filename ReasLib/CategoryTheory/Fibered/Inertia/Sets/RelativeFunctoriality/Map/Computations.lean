module
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.RelativeFunctoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.RelativeFunctoriality.Map.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Set-fibred relative inertia map computations

Total-functor, object, automorphism, and morphism readouts for the bundled maps.
-/
@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
open scoped Bicategory
namespace FiberedCategoryOver.Sets.RelativeInertia
variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C}
/-- The total functor underlying the relative-to-absolute comparison is neutral. -/
@[simp] theorem toInertia.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toFunctor (toInertia F) =
      (BasedCategory.RelativeInertia.toInertia
        (FiberedCategoryOver.Sets.toBasedFunctor F)).toFunctor := sorry
/-- The relative-to-absolute comparison preserves the source object. -/
@[simp] theorem toInertia.obj (F : X ⟶ Y)
    (A : (FiberedCategoryOver.Sets.relativeInertia F).total) :
    ((FiberedCategoryOver.Sets.toFunctor (toInertia F)).obj A).obj = A.obj := sorry
/-- The relative-to-absolute comparison retains the selected automorphism. -/
@[simp] theorem toInertia.aut (F : X ⟶ Y)
    (A : (FiberedCategoryOver.Sets.relativeInertia F).total) :
    ((FiberedCategoryOver.Sets.toFunctor (toInertia F)).obj A).aut = A.aut := sorry
/-- The relative-to-absolute comparison retains the arrow underlying every morphism. -/
@[simp] theorem toInertia.hom (F : X ⟶ Y)
    {A B : (FiberedCategoryOver.Sets.relativeInertia F).total} (φ : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Sets.toFunctor (toInertia F)).map φ) =
      CategoryTheory.RelativeInertia.hom φ := sorry
/-- The total functor of a relative-inertia square map is the neutral induced map. -/
@[simp] theorem map.toFunctor
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂') (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Sets.toFunctor (map G G' comm) =
      CategoryTheory.RelativeInertia.map (FiberedCategoryOver.Sets.toFunctor G) (FiberedCategoryOver.Sets.toFunctor G')
        (map.squareNatIso G G' comm) := sorry
/-- A relative-inertia square map applies the source-side functor to the underlying object. -/
@[simp] theorem map.obj.underlying
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂') (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Sets.relativeInertia F₁).total) :
    ((FiberedCategoryOver.Sets.toFunctor (map G G' comm)).obj A).obj =
      (FiberedCategoryOver.Sets.toFunctor G).obj A.obj := sorry
/-- A relative-inertia square map applies the source-side functor to the selected automorphism. -/
@[simp] theorem map.obj.aut
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂') (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Sets.relativeInertia F₁).total) :
    ((FiberedCategoryOver.Sets.toFunctor (map G G' comm)).obj A).aut =
      (FiberedCategoryOver.Sets.toFunctor G).mapIso A.aut := sorry
/-- A relative-inertia square map applies its source-side functor to the underlying arrow. -/
@[simp] theorem map.hom
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂') (comm : F₁ ≫ G' ≅ G ≫ F₂)
    {A B : (FiberedCategoryOver.Sets.relativeInertia F₁).total} (φ : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom ((FiberedCategoryOver.Sets.toFunctor (map G G' comm)).map φ) =
      (FiberedCategoryOver.Sets.toFunctor G).map (CategoryTheory.RelativeInertia.hom φ) := sorry
end FiberedCategoryOver.Sets.RelativeInertia
end CategoryTheory
