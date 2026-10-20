module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective.Characterization
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids

universe u

/- Lemma 101.14.5: universal injectivity, surjectivity of the relative
2-diagonal, and lifting of 2-arrows between algebraically closed field-valued
points are equivalent. -/
@[stacks 0CPN] #check (AlgebraicGeometry.AlgebraicStack.UniversallyInjective.tfae :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.AlgebraicStack.UniversallyInjective f,
      AlgebraicGeometry.AlgebraicStack.Surjective (Hom.diagonal.{u + 1, u, u + 1} f),
      AlgebraicGeometry.AlgebraicStack.liftsAlgClosedTwoArrows f])
