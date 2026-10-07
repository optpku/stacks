module

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import StacksCheckRecall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

/- Lemma 29.34.5: the base change of a morphism which is smooth is smooth.
This is exactly the canonical mathlib base-change stability theorem
`AlgebraicGeometry.smooth_isStableUnderBaseChange`. -/
@[stacks 01VB] #check (AlgebraicGeometry.smooth_isStableUnderBaseChange :
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Smooth)

end AlgebraicGeometry
