/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.ToInertia.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Setoid-fibred relative inertia map constructions

Bundled relative-to-absolute inertia and invertible-square maps.  Their total-category
readouts live in `Map.Computations`.
-/

@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Setoids
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
namespace RelativeInertia

/-- Retain the selected automorphism in absolute inertia (`04Z5`). -/
@[stacks 04Z5 "setoid-fibred relative-to-absolute inertia comparison"]
def toInertia (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.relativeInertia F ⟶ FiberedCategoryOver.Setoids.inertia X :=
  FiberedCategoryOver.Setoids.ofBasedFunctor
    (BasedCategory.RelativeInertia.toInertia (FiberedCategoryOver.Setoids.toBasedFunctor F))

/-- The underlying based functor of the relative-to-absolute inertia map. -/
@[simp] theorem toInertia.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toBasedFunctor (toInertia F) =
      BasedCategory.RelativeInertia.toInertia (FiberedCategoryOver.Setoids.toBasedFunctor F) := sorry

/-- An invertibly commuting square induces a map on relative inertia (`04Z4`). -/
@[stacks 04Z4 "setoid-fibred relative-inertia square map"]
def map {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'} (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Setoids.relativeInertia F₁ ⟶ FiberedCategoryOver.Setoids.relativeInertia F₂ :=
  FiberedCategoryOver.Setoids.ofBasedFunctor
    (BasedCategory.RelativeInertia.map (FiberedCategoryOver.Setoids.toBasedFunctor G)
      (FiberedCategoryOver.Setoids.toBasedFunctor G')
      (FiberedCategoryOver.Setoids.toBasedFunctorIso comm))

/-- Forgetting the setoid-fibration owner recovers the neutral based map. -/
@[simp] theorem map.toBasedFunctor {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'} (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Setoids.toBasedFunctor (map G G' comm) =
      BasedCategory.RelativeInertia.map (FiberedCategoryOver.Setoids.toBasedFunctor G)
        (FiberedCategoryOver.Setoids.toBasedFunctor G')
        (FiberedCategoryOver.Setoids.toBasedFunctorIso comm) := sorry

end RelativeInertia
end FiberedCategoryOver.Setoids
end CategoryTheory
