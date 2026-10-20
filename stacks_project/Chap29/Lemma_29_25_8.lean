/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import StacksCheckRecall

/- Lemma 29.25.8: The base change of a flat morphism is flat. -/
@[stacks 01U9] #check
  (AlgebraicGeometry.Flat.isStableUnderBaseChange :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Flat)
