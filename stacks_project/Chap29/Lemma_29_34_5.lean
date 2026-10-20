/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
