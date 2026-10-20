module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Diagonal

/-!
# Diagonal of a quotient stack

The isomorphism presheaves of the quotient stack of a groupoid in algebraic
spaces are algebraic spaces, and its diagonal is representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The isomorphism presheaves of the quotient stack of a groupoid in algebraic
spaces are algebraic spaces. -/
theorem isomorphismPresheaf_isAlgebraicSpace {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    isomorphismPresheaf.isAlgebraicSpace (SmallQuotient.quotientStack G) :=
  sorry

/-- The diagonal of the quotient stack of a groupoid in algebraic spaces is
representable by algebraic spaces. -/
@[stacks 04WZ]
theorem relativelyRepresentableByAlgebraicSpaces_diagonal
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
        (SmallQuotient.quotientStack G)) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
