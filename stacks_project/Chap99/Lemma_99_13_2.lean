/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.Diagonal
import StacksCheckRecall

/-!
# Lemma 99.13.2

The diagonal of `Spaces'_{fp, flat, proper}` is representable by algebraic
spaces.
-/

universe u

/- Lemma 99.13.2: the diagonal of finitely presented, flat, proper algebraic
spaces is representable by algebraic spaces. -/
@[stacks 0D1F] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.relativelyRepresentableByAlgebraicSpaces_diagonal :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.GroupScheme.Classifying.relativelyRepresentableByAlgebraicSpaces
        (AlgebraicGeometry.AlgebraicSpace.CohStack.diagonal
          (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.toGroupoids S)))

