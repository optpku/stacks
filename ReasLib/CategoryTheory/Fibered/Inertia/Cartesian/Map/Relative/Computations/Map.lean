module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Relative.Construction

/-!
# Computations for cartesian relative-inertia square maps

This leaf exposes based, total, object, automorphism, and underlying-arrow formulas for the
invertibly commuting square action.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.map

variable {C : Type u} [Category.{v} C]

/-- Forgetting the fibred structure from a relative-inertia square map recovers the canonical
based relative-inertia map. -/
@[simp]
theorem toBasedFunctor
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.toBasedFunctor (map G G' comm) =
      BasedCategory.RelativeInertia.map
        (FiberedCategoryOver.toBasedFunctor G)
        (FiberedCategoryOver.toBasedFunctor G')
        (FiberedCategoryOver.toBasedFunctorIso comm) := sorry

/-- The total functor of a fibred relative-inertia square map is the neutral relative-inertia
map induced by the underlying functor square. -/
@[simp]
theorem toFunctor
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.toFunctor (map G G' comm) =
      CategoryTheory.RelativeInertia.map
        (FiberedCategoryOver.toFunctor G) (FiberedCategoryOver.toFunctor G')
        (BasedNatIso.toNatIso (FiberedCategoryOver.toBasedFunctorIso comm)) := sorry

/-- A fibred relative-inertia square map applies its source-side functor to the underlying
object. -/
@[simp]
theorem obj.underlying
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.relativeInertia F₁).total) :
    ((FiberedCategoryOver.toFunctor (map G G' comm)).obj A).obj =
      (FiberedCategoryOver.toFunctor G).obj A.obj := sorry

/-- A fibred relative-inertia square map applies its source-side functor to the selected
automorphism. -/
@[simp]
theorem obj.aut
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.relativeInertia F₁).total) :
    ((FiberedCategoryOver.toFunctor (map G G' comm)).obj A).aut =
      (FiberedCategoryOver.toFunctor G).mapIso A.aut := sorry

/-- A fibred relative-inertia square map applies its source-side functor to the arrow underlying
each morphism. -/
@[simp]
theorem hom
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    {A B : (FiberedCategoryOver.relativeInertia F₁).total} (φ : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toFunctor (map G G' comm)).map φ) =
      (FiberedCategoryOver.toFunctor G).map
        (CategoryTheory.RelativeInertia.hom φ) := sorry

end FiberedCategoryOver.RelativeInertia.map

end CategoryTheory
