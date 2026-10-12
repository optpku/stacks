/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed.RelativeDiagonal.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Comparison.Construction
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Fibered.Closure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibred relative-inertia comparison construction

This leaf owns the fixed fibred-category comparison from relative inertia to the
self-two-fibre-product of the relative diagonal.  Projection readouts live in
`Comparison.Computations`.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

section FixedOwner

variable {X Y :
  FiberedCategoryOver.{u, v, max w (max u v), v} C}

/-- The neutral relative-inertia comparison preserves strongly cartesian morphisms. -/
theorem diagonalComparison.preservesStronglyCartesian (F : X ⟶ Y) :
    (BasedFunctor.RelativeInertia.diagonalComparison
      (toBasedFunctor F)).PreservesStronglyCartesian := sorry
/- Proof strategy: the comparison admits a based quasi-inverse, so preservation follows from
`BasedFunctor.IsEquivalence.isStronglyCartesian_map`. -/

/-- The canonical comparison from relative inertia to the self-two-fibre-product of the relative
diagonal, retained in the fixed bicategory of fibred categories. -/
@[stacks 034H "fibred relative-inertia diagonal comparison"]
def diagonalComparison (F : X ⟶ Y) :
    relativeInertia F ⟶
      LocallyInduced.TwoFibreProduct.apex
        (RelativeInertia.relativeDiagonal F)
        (RelativeInertia.relativeDiagonal F) :=
  ofBasedFunctor
    (BasedFunctor.RelativeInertia.diagonalComparison (toBasedFunctor F))
    (RelativeInertia.diagonalComparison.preservesStronglyCartesian F)

/-- Forgetting the fibred-category owner from the canonical comparison recovers the neutral
based relative-inertia comparison. -/
@[simp]
theorem diagonalComparison.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor (RelativeInertia.diagonalComparison F) =
      BasedFunctor.RelativeInertia.diagonalComparison (FiberedCategoryOver.toBasedFunctor F) := sorry

/-- The total functor underlying the fibred relative-inertia comparison is the neutral based
comparison functor. -/
@[simp]
theorem diagonalComparison.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison F) =
      (BasedFunctor.RelativeInertia.diagonalComparison
        (FiberedCategoryOver.toBasedFunctor F)).toFunctor := sorry

end FixedOwner

end FiberedCategoryOver.RelativeInertia
end CategoryTheory
