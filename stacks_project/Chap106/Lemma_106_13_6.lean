/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.WellNighAffine.Moduli
import StacksCheckRecall

/-!
# Uniform categorical moduli spaces of well-nigh affine stacks

If an algebraic stack is well-nigh affine, then a uniform categorical moduli
space in the category of affine schemes is a uniform categorical moduli space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

/- Lemma 106.13.6. Let the algebraic stack `X` be well-nigh affine. The morphism
`f : X ⟶ M.toGroupoids` of Lemma 106.13.4 is a uniform categorical moduli space. -/
@[stacks 0DUR] #check
  (AlgebraicGeometry.AlgebraicStack.IsWellNighAffine.instIsUniformCategoricalModuliSpace :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      [AlgebraicGeometry.AlgebraicStack.IsWellNighAffine X] {M : AlgebraicSpace S}
      (f : X ⟶ M.toGroupoids)
      [AlgebraicGeometry.AlgebraicStack.IsUniformCategoricalModuliSpaceIn
        AlgebraicSpace.IsAffine f],
      AlgebraicGeometry.AlgebraicStack.IsUniformCategoricalModuliSpace f)
