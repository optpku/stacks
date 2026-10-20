/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap108.Lemma_108_4_1_Affine
public import stacks_project.Chap108.Lemma_108_4_1_Diagonal
public import stacks_project.Chap108.Lemma_108_4_1_FinitePresentation
public import stacks_project.Chap108.Lemma_108_8_3_Map

/-!
# Lemma 108.8.1

The relative diagonal of the Picard stack over `B` is affine and of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Picard
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.8.1 (1): the relative diagonal `CohStack.Hom.diagonal (toBase f)` of
`Pic_{X/B}` over `B` is affine. -/
@[stacks 0DMA]
instance instAffine_diagonal (f : X ⟶ B) [Flat f] [FinitePresentation f]
    [Proper f] : CohStack.Hom.Affine (CohStack.Hom.diagonal (toBase f)) :=
  sorry

/-- Lemma 108.8.1 (2): the relative diagonal `CohStack.Hom.diagonal (toBase f)` of
`Pic_{X/B}` over `B` is of finite presentation. -/
@[stacks 0DMA]
instance instFinitePresentation_diagonal (f : X ⟶ B) [Flat f]
    [FinitePresentation f] [Proper f] :
    CohStack.Hom.FinitePresentation (CohStack.Hom.diagonal (toBase f)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
