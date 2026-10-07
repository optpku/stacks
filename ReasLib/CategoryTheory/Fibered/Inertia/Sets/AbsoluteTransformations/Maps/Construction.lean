module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Equivalence.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Setoids.FromSets
import Mathlib.Tactic.CrossRefAttribute

/-!
# Set-fibred inertia transformation constructions

The owner definitions for forgetting, the identity section, and the objectwise equivalence.
-/

@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
open scoped Bicategory
namespace FiberedCategoryOver.Sets.Inertia
variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}

/-- Forget the selected automorphism. -/
@[stacks 042H "set-fibred inertia structure map"]
def forget (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Sets.inertia X ⟶ X :=
  FiberedCategoryOver.Sets.ofBasedFunctor
    (BasedCategory.Inertia.forget X.toBasedCategory)

/-- Equip every object with its identity automorphism. -/
@[stacks 04Z3 "set-fibred inertia neutral section"]
def identitySection (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    X ⟶ FiberedCategoryOver.Sets.inertia X :=
  FiberedCategoryOver.Sets.ofBasedFunctor
    (BasedCategory.Inertia.identitySection X.toBasedCategory)

/-- Inertia of a category fibred in sets is canonically equivalent to the original category. -/
@[stacks 04Z3 "set-fibred inertia equivalence"]
def forget.equivalence (X : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Sets.inertia X ≌ X :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (BasedCategory.Inertia.forget.equivalenceOf X.toBasedCategory
      (BasedCategory.isFiberedInSets.le_isFiberedInSetoids X.toBasedCategory X.2))
end FiberedCategoryOver.Sets.Inertia
end CategoryTheory
