module

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import StacksCheckRecall

/- Lemma 29.25.8: The base change of a flat morphism is flat. -/
@[stacks 01U9] #check
  (AlgebraicGeometry.Flat.isStableUnderBaseChange :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Flat)
