/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap99.Lemma_99_15_2
public import stacks_project.Chap108.Lemma_108_4_8_Algebraic
public import stacks_project.Chap108.Lemma_108_4_1_FinitePresentation
public import stacks_project.Chap108.Lemma_108_4_2_QuasiSeparated

/-!
# Lemma 109.5.1

The object diagonal of `Curves` is separated and of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- Lemma 109.5.1 (1): the object diagonal `CohStack.diagonal (toGroupoids S)`
of `Curves` is separated as a morphism of algebraic spaces on scheme-slice
tests. -/
@[stacks 0DSQ]
theorem has_separated_diagonal (S : Scheme.{u}) :
    CohStack.Hom.has (@AlgebraicSpace.Separated S)
      (CohStack.diagonal (toGroupoids S)) :=
  sorry

/-- Lemma 109.5.1 (2): the object diagonal `CohStack.diagonal (toGroupoids S)`
of `Curves` is of finite presentation. -/
@[stacks 0DSQ]
instance instFinitePresentation_diagonal (S : Scheme.{u}) :
    CohStack.Hom.FinitePresentation (CohStack.diagonal (toGroupoids S)) :=
  sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
