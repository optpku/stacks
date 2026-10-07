module

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.2.5: A composition of closed immersions is a closed immersion. -/
@[stacks 01QS] #check
  (@AlgebraicGeometry.IsClosedImmersion.comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.IsClosedImmersion f] [AlgebraicGeometry.IsClosedImmersion g],
      AlgebraicGeometry.IsClosedImmersion (f ≫ g))
