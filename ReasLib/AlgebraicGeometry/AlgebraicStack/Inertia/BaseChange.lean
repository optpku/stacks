module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Comparison.Construction
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Base change of the inertia comparison

Equivalence over the base of the canonical inertia comparison of an algebraic
stack morphism is preserved by cartesian base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Inertia

/-- In a cartesian square of algebraic stacks, equivalence over the base of
the canonical inertia comparison for `f` implies equivalence over the base of
the canonical inertia comparison for the second projection. -/
@[stacks 0DUB]
theorem comparison_isEquivalence_of_isBilimit {S : Scheme.{u}}
    {X Y Y' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Y'] {f : X ⟶ Y} {g : Y' ⟶ Y}
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    (hf : (CategoryTheory.FiberedCategoryOver.Groupoids.toBasedFunctor
      (comparison f)).IsEquivalence) :
    (CategoryTheory.FiberedCategoryOver.Groupoids.toBasedFunctor
      (comparison c.snd)).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Inertia
