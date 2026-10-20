module

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import StacksCheckRecall

/- Lemma 29.36.4: the base change of a morphism which is étale is étale. -/
@[stacks 02GO] #check
  (AlgebraicGeometry.Etale.etale_isStableUnderBaseChange :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Etale)
