module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Nagata.FiniteType
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.26.1: If the target of a locally-of-finite-type morphism of algebraic spaces
is Nagata, then its source is Nagata. -/
@[stacks 0BAU] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.isNagata :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      [AlgebraicGeometry.AlgebraicSpace.IsNagata Y], AlgebraicGeometry.AlgebraicSpace.IsNagata X)
