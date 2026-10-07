module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Detection.Absolute
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stable-universe cartesian inertia maps

This file owns the canonical forgetful map and identity section in the universe-stable
cartesian setting. Their computations and naturality laws are layered separately.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]

variable {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C}

/-- Forgetting the selected automorphism defines a morphism of fibred categories. -/
@[stacks 042H "(2) cartesian inertia structure map"]
def forget (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.inertia X ⟶ X :=
  FiberedCategoryOver.ofBasedFunctor
    (BasedCategory.Inertia.forget X.toBasedCategory)
    (BasedCategory.Inertia.forget.preservesStronglyCartesian X.toBasedCategory)

/-- Equipping every object with its identity automorphism defines a morphism of fibred
categories. -/
@[stacks 04Z3 "(2) cartesian inertia neutral section"]
def identitySection (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    X ⟶ FiberedCategoryOver.inertia X :=
  FiberedCategoryOver.ofBasedFunctor
    (BasedCategory.Inertia.identitySection X.toBasedCategory)
    (BasedCategory.Inertia.identitySection.preservesStronglyCartesian X.toBasedCategory)

end FiberedCategoryOver.Inertia

end CategoryTheory
