module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.OpenImmersion

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack

universe u

/- Lemma 108.4.5: an open immersion between algebraic spaces separated and of
finite presentation over `B` induces an open immersion of coherent-sheaf stacks
by fibrewise pushforward. -/
@[stacks 0DNA] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.instOpenImmersion_map :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (π : X ⟶ Y) (y : Y ⟶ B)
    [IsOpenImmersion π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y],
    OpenImmersion (mapOfOpenImmersion π y))
