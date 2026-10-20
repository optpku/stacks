/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Polarized.AlgebraicStack
import StacksCheckRecall

/-!
# Lemma 108.11.2

The structure morphism Polarized ⟶ specZ is quasi-separated and locally of
finite presentation.
-/

@[expose] public section

universe u

/- Lemma 108.11.2 (1): the structure morphism Polarized ⟶ specZ is
quasi-separated. -/
@[stacks 0DPU] #check
  (AlgebraicGeometry.Polarized.instQuasiSeparated_baseProjection :
    AlgebraicGeometry.AlgebraicStack.QuasiSeparated
      (CategoryTheory.FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1}
        AlgebraicGeometry.Polarized.toGroupoidsOverSpecZ))

/- Lemma 108.11.2 (2): the structure morphism Polarized ⟶ specZ is locally of
finite presentation. -/
@[stacks 0DPU] #check
  (AlgebraicGeometry.Polarized.instLocallyOfFinitePresentation_baseProjection :
    AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
      (CategoryTheory.FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1}
        AlgebraicGeometry.Polarized.toGroupoidsOverSpecZ))
