module

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import StacksCheckRecall

/- Lemma 29.44.6 (1): a base change of a finite morphism is finite. -/
@[stacks 01WL] #check
  (AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.IsFinite)

/- Lemma 29.44.6 (2): a base change of an integral morphism is integral. -/
@[stacks 01WL] #check
  (AlgebraicGeometry.IsIntegralHom.instIsStableUnderBaseChangeScheme :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.IsIntegralHom)
