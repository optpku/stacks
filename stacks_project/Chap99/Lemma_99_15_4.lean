/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Diagonal
import StacksCheckRecall

/-!
# Lemma 99.15.4

The diagonal of `Curves` is representable by algebraic spaces.
-/

universe u

/- Lemma 99.15.4: the diagonal
`Δ : Curves ⟶ Curves × Curves` is representable by algebraic spaces. -/
@[stacks 0D53] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.relativelyRepresentableByAlgebraicSpaces_diagonal :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.GroupScheme.Classifying.relativelyRepresentableByAlgebraicSpaces
        (AlgebraicGeometry.AlgebraicSpace.CohStack.diagonal
          (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.toGroupoids S)))
