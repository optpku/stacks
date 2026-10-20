/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap108.Lemma_108_4_1_Affine
public import stacks_project.Chap108.Lemma_108_4_1_Diagonal
public import stacks_project.Chap108.Lemma_108_4_1_FinitePresentation
public import stacks_project.Chap108.Lemma_108_4_3_Map

/-!
# Lemma 108.4.1

The relative diagonal of the stack of coherent sheaves over `B` is affine and of
finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.4.1 (1): the relative diagonal `Hom.diagonal (forget f)` of
`toGroupoids f` over `B` is affine. -/
@[stacks 0DLY]
instance instAffine_diagonal (f : X ⟶ B) [FinitePresentation f] [Separated f] :
    Hom.Affine (Hom.diagonal (forget f)) :=
  sorry

/-- Lemma 108.4.1 (2): the relative diagonal `Hom.diagonal (forget f)` of
`toGroupoids f` over `B` is of finite presentation. -/
@[stacks 0DLY]
instance instFinitePresentation_diagonal (f : X ⟶ B) [FinitePresentation f]
    [Separated f] :
    Hom.FinitePresentation (Hom.diagonal (forget f)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
