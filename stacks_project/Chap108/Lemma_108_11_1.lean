/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Polarized.Diagonal
import StacksCheckRecall

/-!
# Lemma 108.11.1

The object diagonal of Polarized is separated and of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 108.11.1 (1): the object diagonal
`Δ : Polarized ⟶ Polarized × Polarized` is separated as a morphism
representable by algebraic spaces. -/
@[stacks 0DPT]
#check (AlgebraicGeometry.Polarized.has_separated_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.Separated AlgebraicGeometry.Polarized.specZ)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
        AlgebraicGeometry.Polarized.toGroupoidsOverSpecZ))

/- Lemma 108.11.1 (2): the object diagonal
`Δ : Polarized ⟶ Polarized × Polarized` is of finite presentation as a morphism
representable by algebraic spaces. -/
@[stacks 0DPT]
#check (AlgebraicGeometry.Polarized.has_finitePresentation_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.FinitePresentation AlgebraicGeometry.Polarized.specZ)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
        AlgebraicGeometry.Polarized.toGroupoidsOverSpecZ))
