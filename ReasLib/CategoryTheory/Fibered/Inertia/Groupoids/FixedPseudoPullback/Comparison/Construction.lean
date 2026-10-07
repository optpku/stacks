module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback.RelativeDiagonal.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Comparison.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed groupoid-fibred relative-inertia comparison construction

The owner-level forward comparison from relative inertia to the self
two-fibre-product of the fixed relative diagonal.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Groupoids.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

section FixedPseudoPullbackOwner

variable {X Y :
  FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}

/-- The owner-level comparison from relative inertia to the self-two-fibre-product of the
relative diagonal. -/
@[stacks 034H "fixed groupoid-fibred relative-inertia diagonal comparison"]
def diagonalComparison (F : X ⟶ Y) :
    relativeInertia F ⟶
      CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F) :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedFunctor.RelativeInertia.diagonalComparison (toBasedFunctor F))

/-- Forgetting the groupoid-fibration owner from the relative-inertia comparison recovers the
neutral based comparison. -/
@[simp]
theorem diagonalComparison.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (diagonalComparison F) =
      BasedFunctor.RelativeInertia.diagonalComparison
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) := sorry

/-- The total functor underlying the groupoid-fibred relative-inertia comparison is the neutral
based comparison functor. -/
@[simp]
theorem diagonalComparison.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toFunctor (diagonalComparison F) =
      (BasedFunctor.RelativeInertia.diagonalComparison
        (FiberedCategoryOver.Groupoids.toBasedFunctor F)).toFunctor := sorry

/-- The based diagonal comparison preserves strongly cartesian morphisms, exposing the
automatic groupoid-target fact needed by ambient fibred-category constructions. -/
theorem diagonalComparison.preservesStronglyCartesian (F : X ⟶ Y) :
    (BasedFunctor.RelativeInertia.diagonalComparison
      (FiberedCategoryOver.Groupoids.toBasedFunctor F)).PreservesStronglyCartesian := sorry

end FixedPseudoPullbackOwner

end FiberedCategoryOver.Groupoids.RelativeInertia

end CategoryTheory
