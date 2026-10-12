/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Detection.Relative
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cartesian maps for relative inertia

This file owns the cartesian map induced by an invertible square of fibred-category
morphisms and the cartesian comparison from relative to absolute inertia. Their based,
total, and component computations are layered separately.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

namespace map

/-- The based relative-inertia map induced by an invertible square of fibred-category morphisms
preserves strongly cartesian arrows. -/
@[stacks 04Z4 "cartesian relative-inertia square preservation"]
theorem preservesStronglyCartesian
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    (BasedCategory.RelativeInertia.map
      (toBasedFunctor G) (toBasedFunctor G')
      (FiberedCategoryOver.toBasedFunctorIso comm)).PreservesStronglyCartesian := sorry
/- Proof strategy: apply
`BasedCategory.RelativeInertia.map.preservesStronglyCartesian` to `F₁.property` and `G.property`;
the remaining square is `FiberedCategoryOver.toBasedFunctorIso comm`. -/

end map

/-- An invertibly commuting square of cartesian morphisms of fibred categories induces the
canonical cartesian map on relative inertia. The horizontal arrows are inferred from the square. -/
@[stacks 04Z4 "(1) cartesian relative-inertia square map"]
def map
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.relativeInertia F₁ ⟶
      FiberedCategoryOver.relativeInertia F₂ :=
  FiberedCategoryOver.ofBasedFunctor
    (BasedCategory.RelativeInertia.map
      (toBasedFunctor G) (toBasedFunctor G')
      (FiberedCategoryOver.toBasedFunctorIso comm))
    (map.preservesStronglyCartesian G G' comm)

namespace toInertia

/-- The based relative-to-absolute inertia comparison of a fibred-category morphism preserves
strongly cartesian arrows. -/
@[stacks 04Z5 "cartesian relative-to-absolute preservation"]
theorem preservesStronglyCartesian (F : X ⟶ Y) :
    (BasedCategory.RelativeInertia.toInertia
      (FiberedCategoryOver.toBasedFunctor F)).PreservesStronglyCartesian := sorry
/- Proof strategy: apply
`BasedCategory.RelativeInertia.toInertia.preservesStronglyCartesian` to `F.property`. -/

end toInertia

/-- Retaining the selected automorphism defines the canonical cartesian comparison from relative
to absolute inertia in the bicategory of fibred categories. -/
@[stacks 04Z5 "cartesian relative-to-absolute inertia comparison"]
def toInertia (F : X ⟶ Y) :
    FiberedCategoryOver.relativeInertia F ⟶ FiberedCategoryOver.inertia X :=
  FiberedCategoryOver.ofBasedFunctor
    (BasedCategory.RelativeInertia.toInertia
      (FiberedCategoryOver.toBasedFunctor F))
    (toInertia.preservesStronglyCartesian F)

end FiberedCategoryOver.RelativeInertia

end CategoryTheory

/- Axiom audit: both cartesian maps store the corresponding canonical based functor
definitionally. Any new `sorryAx` is confined to strongly-cartesian-preservation or
owner-membership proof fields. -/
