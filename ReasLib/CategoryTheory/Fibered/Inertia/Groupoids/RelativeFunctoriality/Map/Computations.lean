module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Map.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Groupoid-fibred relative inertia map computations

Total-functor, object, automorphism, and morphism readouts for the bundled maps.
-/

@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Groupoids
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
namespace RelativeInertia

/-- The total functor of the groupoid-fibred relative-to-absolute inertia map is the neutral total functor. -/
@[simp] theorem toInertia.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toFunctor (toInertia F) =
      (BasedCategory.RelativeInertia.toInertia (FiberedCategoryOver.Groupoids.toBasedFunctor F)).toFunctor := sorry
/-- The relative-to-absolute inertia map preserves the underlying source object. -/
@[simp] theorem toInertia.obj (F : X ⟶ Y) (A : (FiberedCategoryOver.Groupoids.relativeInertia F).total) :
    ((FiberedCategoryOver.Groupoids.toFunctor (toInertia F)).obj A).obj = A.obj := sorry
/-- The relative-to-absolute inertia map retains the selected automorphism. -/
@[simp] theorem toInertia.aut (F : X ⟶ Y) (A : (FiberedCategoryOver.Groupoids.relativeInertia F).total) :
    ((FiberedCategoryOver.Groupoids.toFunctor (toInertia F)).obj A).aut = A.aut := sorry
/-- The relative-to-absolute inertia map retains the arrow underlying every morphism. -/
@[simp] theorem toInertia.hom (F : X ⟶ Y)
    {A B : (FiberedCategoryOver.Groupoids.relativeInertia F).total} (φ : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom ((FiberedCategoryOver.Groupoids.toFunctor (toInertia F)).map φ) =
      CategoryTheory.RelativeInertia.hom φ := sorry

/-- The total functor of a groupoid-fibred relative-inertia square map is the neutral map
induced by its underlying functor square. -/
@[simp] theorem map.toFunctor {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂') (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Groupoids.toFunctor (map G G' comm) =
      CategoryTheory.RelativeInertia.map (FiberedCategoryOver.Groupoids.toFunctor G)
        (FiberedCategoryOver.Groupoids.toFunctor G')
        (BasedNatIso.toNatIso (FiberedCategoryOver.Groupoids.toBasedFunctorIso comm)) := sorry
/-- A groupoid-fibred relative-inertia square map applies its source-side functor to the underlying object. -/
@[simp] theorem map.obj.underlying {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'} (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) (A : (FiberedCategoryOver.Groupoids.relativeInertia F₁).total) :
    ((FiberedCategoryOver.Groupoids.toFunctor (map G G' comm)).obj A).obj =
      (FiberedCategoryOver.Groupoids.toFunctor G).obj A.obj := sorry
/-- A groupoid-fibred relative-inertia square map applies its source-side functor to the selected automorphism. -/
@[simp] theorem map.obj.aut {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'} (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) (A : (FiberedCategoryOver.Groupoids.relativeInertia F₁).total) :
    ((FiberedCategoryOver.Groupoids.toFunctor (map G G' comm)).obj A).aut =
      (FiberedCategoryOver.Groupoids.toFunctor G).mapIso A.aut := sorry
/-- A groupoid-fibred relative-inertia square map applies its source-side functor to the underlying arrow. -/
@[simp] theorem map.hom {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'} (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    {A B : (FiberedCategoryOver.Groupoids.relativeInertia F₁).total} (φ : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom ((FiberedCategoryOver.Groupoids.toFunctor (map G G' comm)).map φ) =
      (FiberedCategoryOver.Groupoids.toFunctor G).map (CategoryTheory.RelativeInertia.hom φ) := sorry
end RelativeInertia
end FiberedCategoryOver.Groupoids
end CategoryTheory
