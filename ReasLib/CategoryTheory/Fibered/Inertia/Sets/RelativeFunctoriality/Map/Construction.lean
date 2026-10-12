/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.ToInertia.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Set-fibred relative inertia map constructions

Bundled relative-to-absolute inertia and invertible-square maps. Their comparison and
total-category readouts live in the focused sibling modules.
-/
@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
open scoped Bicategory
namespace FiberedCategoryOver.Sets.RelativeInertia
variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C}
/-- Retain the selected relative automorphism in absolute inertia (`04Z5`). -/
@[stacks 04Z5 "set-fibred relative-to-absolute inertia comparison"]
def toInertia (F : X ⟶ Y) : FiberedCategoryOver.Sets.relativeInertia F ⟶ FiberedCategoryOver.Sets.inertia X :=
  FiberedCategoryOver.Sets.ofBasedFunctor
    (BasedCategory.RelativeInertia.toInertia
      (FiberedCategoryOver.Sets.toBasedFunctor F))
/-- The based functor underlying the relative-to-absolute comparison is the neutral map. -/
@[simp] theorem toInertia.toBasedFunctor (F : X ⟶ Y) : FiberedCategoryOver.Sets.toBasedFunctor (toInertia F) =
  BasedCategory.RelativeInertia.toInertia (FiberedCategoryOver.Sets.toBasedFunctor F) := sorry
/-- An invertibly commuting square induces a map on relative inertia (`04Z4`). -/
@[stacks 04Z4 "set-fibred relative-inertia square map"]
def map
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂') (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Sets.relativeInertia F₁ ⟶ FiberedCategoryOver.Sets.relativeInertia F₂ :=
  FiberedCategoryOver.Sets.ofBasedFunctor (BasedCategory.RelativeInertia.map (FiberedCategoryOver.Sets.toBasedFunctor G)
    (FiberedCategoryOver.Sets.toBasedFunctor G') (Bicategory.InducedBicategory.Iso.toAmbient comm))
/-- Forgetting the set-fibration owner from a relative-inertia square map recovers the neutral
based map. -/
@[simp] theorem map.toBasedFunctor
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂') (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Sets.toBasedFunctor (map G G' comm) = BasedCategory.RelativeInertia.map
      (FiberedCategoryOver.Sets.toBasedFunctor G) (FiberedCategoryOver.Sets.toBasedFunctor G')
      (Bicategory.InducedBicategory.Iso.toAmbient comm) := sorry
end FiberedCategoryOver.Sets.RelativeInertia
end CategoryTheory
