/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Relative.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stable cartesian relative-inertia maps

This file owns the forgetful map and identity section for relative inertia in the stable
universe. Computation formulas are provided by the companion leaf.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C}

/-- Forgetting the selected relative automorphism defines the cartesian relative-inertia
structure map. -/
@[stacks 042H "(1) cartesian relative-inertia structure map"]
def forget (F : X ⟶ Y) : FiberedCategoryOver.relativeInertia F ⟶ X :=
  FiberedCategoryOver.ofBasedFunctor
    (BasedCategory.RelativeInertia.forget
      (FiberedCategoryOver.toBasedFunctor F))
    (BasedCategory.RelativeInertia.forget.preservesStronglyCartesian
      (FiberedCategoryOver.toBasedFunctor F) F.property)

/-- Equipping each source object with its identity automorphism defines the cartesian relative
identity section. -/
@[stacks 04Z3 "(1) cartesian relative-inertia neutral section"]
def identitySection (F : X ⟶ Y) : X ⟶ FiberedCategoryOver.relativeInertia F :=
  FiberedCategoryOver.ofBasedFunctor
    (BasedCategory.RelativeInertia.identitySection
      (FiberedCategoryOver.toBasedFunctor F))
    (BasedCategory.RelativeInertia.identitySection.preservesStronglyCartesian
      (FiberedCategoryOver.toBasedFunctor F))

end FiberedCategoryOver.RelativeInertia

end CategoryTheory
