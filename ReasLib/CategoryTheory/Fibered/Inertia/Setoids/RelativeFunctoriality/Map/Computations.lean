module
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.RelativeFunctoriality.Map.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Setoid-fibred relative inertia map computations

Total-functor, object, automorphism, and morphism readouts for the bundled maps.
-/

@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Setoids
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
namespace RelativeInertia
variable {X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C}

/-- The total functor of `toInertia` is the neutral total functor. -/
@[simp] theorem toInertia.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toFunctor (toInertia F) =
      (BasedCategory.RelativeInertia.toInertia (FiberedCategoryOver.Setoids.toBasedFunctor F)).toFunctor := sorry
/-- `toInertia` preserves the underlying source object. -/
@[simp] theorem toInertia.obj (F : X ⟶ Y) (A : (FiberedCategoryOver.Setoids.relativeInertia F).total) :
    ((FiberedCategoryOver.Setoids.toFunctor (toInertia F)).obj A).obj = A.obj := sorry
/-- `toInertia` retains the selected automorphism. -/
@[simp] theorem toInertia.aut (F : X ⟶ Y) (A : (FiberedCategoryOver.Setoids.relativeInertia F).total) :
    ((FiberedCategoryOver.Setoids.toFunctor (toInertia F)).obj A).aut = A.aut := sorry
/-- `toInertia` retains the arrow underlying every morphism. -/
@[simp] theorem toInertia.hom (F : X ⟶ Y)
    {A B : (FiberedCategoryOver.Setoids.relativeInertia F).total} (φ : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom ((FiberedCategoryOver.Setoids.toFunctor (toInertia F)).map φ) =
      CategoryTheory.RelativeInertia.hom φ := sorry

/-- The total functor of a square map is the neutral induced map. -/
@[simp] theorem map.toFunctor {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'} (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Setoids.toFunctor (map G G' comm) =
      CategoryTheory.RelativeInertia.map (FiberedCategoryOver.Setoids.toFunctor G)
        (FiberedCategoryOver.Setoids.toFunctor G')
        (BasedNatIso.toNatIso (FiberedCategoryOver.Setoids.toBasedFunctorIso comm)) := sorry
/-- A square map applies its source-side functor to the underlying object. -/
@[simp] theorem map.obj.underlying {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'} (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) (A : (FiberedCategoryOver.Setoids.relativeInertia F₁).total) :
    ((FiberedCategoryOver.Setoids.toFunctor (map G G' comm)).obj A).obj =
      (FiberedCategoryOver.Setoids.toFunctor G).obj A.obj := sorry
/-- A square map applies its source-side functor to the selected automorphism. -/
@[simp] theorem map.obj.aut {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'} (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) (A : (FiberedCategoryOver.Setoids.relativeInertia F₁).total) :
    ((FiberedCategoryOver.Setoids.toFunctor (map G G' comm)).obj A).aut =
      (FiberedCategoryOver.Setoids.toFunctor G).mapIso A.aut := sorry
/-- A square map applies its source-side functor to the underlying arrow. -/
@[simp] theorem map.hom {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'} (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    {A B : (FiberedCategoryOver.Setoids.relativeInertia F₁).total} (φ : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom ((FiberedCategoryOver.Setoids.toFunctor (map G G' comm)).map φ) =
      (FiberedCategoryOver.Setoids.toFunctor G).map (CategoryTheory.RelativeInertia.hom φ) := sorry
end RelativeInertia
end FiberedCategoryOver.Setoids
end CategoryTheory
