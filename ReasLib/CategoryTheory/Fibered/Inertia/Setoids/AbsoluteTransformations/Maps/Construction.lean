module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Equivalence.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Objects.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Setoid-fibred inertia transformation constructions

The owner definitions for forgetting, the identity section, and the objectwise equivalence.
-/

@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Setoids
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
namespace Inertia
variable {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}

/-- Forget the selected automorphism. -/
@[stacks 042H "(2) setoid-fibred inertia structure map"]
def forget (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Setoids.inertia X ⟶ X :=
  FiberedCategoryOver.Setoids.ofBasedFunctor
    (BasedCategory.Inertia.forget X.toBasedCategory)

/-- Equip every object with its identity automorphism. -/
@[stacks 04Z3 "(2) setoid-fibred inertia neutral section"]
def identitySection (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    X ⟶ FiberedCategoryOver.Setoids.inertia X :=
  FiberedCategoryOver.Setoids.ofBasedFunctor
    (BasedCategory.Inertia.identitySection X.toBasedCategory)

/-- Inertia of a category fibred in setoids is canonically equivalent to the original category. -/
@[stacks 04Z3 "setoid-fibred inertia equivalence"]
def forget.equivalence (X : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Setoids.inertia X ≌ X :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (BasedCategory.Inertia.forget.equivalenceOf X.toBasedCategory X.2)
end Inertia
end FiberedCategoryOver.Setoids
end CategoryTheory
