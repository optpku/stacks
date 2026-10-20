module

public import ReasLib.AlgebraicGeometry.Polarized.Diagonal
import StacksCheckRecall

/-!
# Lemma 99.14.7

The diagonal of Polarized is representable by algebraic spaces.
-/

universe u

/- Lemma 99.14.7. The diagonal of Polarized is representable by algebraic spaces. -/
@[stacks 0D42]
#check (AlgebraicGeometry.Polarized.relativelyRepresentableByAlgebraicSpaces_diagonal :
  AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces
    (CategoryTheory.FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
      AlgebraicGeometry.Polarized.toGroupoidsOverSpecZ))
