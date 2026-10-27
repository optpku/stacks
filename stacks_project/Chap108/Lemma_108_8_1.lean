/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Diagonal
import StacksCheckRecall

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

/- Lemma 108.8.1 (1): the relative diagonal of the Picard stack over `B` is affine. -/
@[stacks 0DMA] #check (AlgebraicGeometry.AlgebraicSpace.Picard.instAffine_diagonal :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f],
    CohStack.Hom.Affine (CohStack.Hom.diagonal (Picard.toBase f)))

/- Lemma 108.8.1 (2): the relative diagonal of the Picard stack over `B` is of
finite presentation. -/
@[stacks 0DMA] #check (AlgebraicGeometry.AlgebraicSpace.Picard.instFinitePresentation_diagonal :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f],
    CohStack.Hom.FinitePresentation (CohStack.Hom.diagonal (Picard.toBase f)))
