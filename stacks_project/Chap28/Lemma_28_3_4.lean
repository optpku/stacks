/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Properties
import StacksCheckRecall

universe u

/- Lemma 28.3.4: A scheme `X` is integral if and only if it is reduced and irreducible. -/
@[stacks 01ON] #check
  (AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.IsIntegral X ↔ IrreducibleSpace X ∧ AlgebraicGeometry.IsReduced X)
