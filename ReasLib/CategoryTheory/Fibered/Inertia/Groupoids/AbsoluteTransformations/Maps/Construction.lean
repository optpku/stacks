/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Objects.Construction
import Mathlib.Tactic.CrossRefAttribute

/-! Groupoid-fibred inertia transformation data owners. -/
@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Groupoids
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
namespace Inertia
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}

/-- Forget the selected automorphism. -/
@[stacks 042H "(2) groupoid-fibred inertia structure map"]
def forget (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.Groupoids.inertia X ⟶ X :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedCategory.Inertia.forget X.toBasedCategory)

/-- Equip every object with its identity automorphism. -/
@[stacks 04Z3 "(2) groupoid-fibred inertia neutral section"]
def identitySection (X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C) :
    X ⟶ FiberedCategoryOver.Groupoids.inertia X :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedCategory.Inertia.identitySection X.toBasedCategory)

end Inertia
end FiberedCategoryOver.Groupoids
end CategoryTheory
