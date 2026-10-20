/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import StacksCheckRecall

/- Lemma 29.36.4: the base change of a morphism which is étale is étale. -/
@[stacks 02GO] #check
  (AlgebraicGeometry.Etale.etale_isStableUnderBaseChange :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Etale)
