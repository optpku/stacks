module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Relative.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Naturality.Construction

/-!
# Construction of cartesian relative-inertia naturality

This module owns the relative-to-absolute comparison for invertibly commuting squares of
cartesian morphisms of fibred categories. Its component readouts are in `Computations`.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.toInertia

variable {C : Type u} [Category.{v} C]

/-- The relative-to-absolute inertia comparison is natural for an invertibly commuting square
of cartesian morphisms of fibred categories. -/
@[stacks 04Z5 "naturality of cartesian relative-to-absolute inertia"]
def naturalityIso
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.RelativeInertia.map G G' comm ≫
        FiberedCategoryOver.RelativeInertia.toInertia F₂ ≅
      FiberedCategoryOver.RelativeInertia.toInertia F₁ ≫
        FiberedCategoryOver.Inertia.map G :=
  FiberedCategoryOver.BasedFunctorIso.lift
    (BasedCategory.RelativeInertia.toInertia.naturalityIso
      (FiberedCategoryOver.toBasedFunctor G)
      (FiberedCategoryOver.toBasedFunctor G')
      (FiberedCategoryOver.toBasedFunctorIso comm))

end FiberedCategoryOver.RelativeInertia.toInertia

end CategoryTheory
