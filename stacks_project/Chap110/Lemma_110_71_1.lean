/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.NonAlgebraic
import StacksCheckRecall

universe u

/- Lemma 110.71.1: The stack in groupoids of flat, proper, finitely presented
algebraic spaces over schemes is not an algebraic stack. -/
@[stacks 0D1R] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.not_isAlgebraic :
    ¬ AlgebraicGeometry.AlgebraicSpace.CohStack.AlgebraicStack
      (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.toGroupoids
        AlgebraicGeometry.AlgebraicSpace.specZ.{u}))
