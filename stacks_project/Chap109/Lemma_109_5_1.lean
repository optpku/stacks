/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Diagonal
import StacksCheckRecall

/-!
# Lemma 109.5.1

The object diagonal of `Curves` is separated and of finite presentation.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 109.5.1 (1): the diagonal of the stack of curves is separated. -/
@[stacks 0DSQ] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.has_separated_diagonal :
    ∀ S : Scheme.{u}, CohStack.Hom.has (@AlgebraicSpace.Separated S)
      (CohStack.diagonal (Spaces.Curves.toGroupoids S)))

/- Lemma 109.5.1 (2): the diagonal of the stack of curves is of finite presentation. -/
@[stacks 0DSQ] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instFinitePresentation_diagonal :
    ∀ S : Scheme.{u},
      CohStack.Hom.FinitePresentation (CohStack.diagonal (Spaces.Curves.toGroupoids S)))
