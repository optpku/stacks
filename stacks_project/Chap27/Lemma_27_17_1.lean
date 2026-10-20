/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap27.Lemma_27_17_1_AssociatedSheaf
public import stacks_project.Chap27.Lemma_27_17_1_Tensor
public import stacks_project.Chap27.Lemma_27_17_1_Shift
public import stacks_project.Chap27.Lemma_27_17_1_BaseChange
import StacksCheckRecall

@[expose] public section

/- Lemma 27.17.1 (1): the canonical local comparison identifies pullback with formula
27.17.0.1. -/
@[stacks 01O7] #check
  AlgebraicGeometry.RelativeProjTwistPresentation.associatedLocalIso

/- Lemma 27.17.1 (2): the local comparison is compatible with pullback. -/
@[stacks 01O7] #check
  AlgebraicGeometry.RelativeProjTwistPresentation.associatedLocalIso_comp

/- Lemma 27.17.1 (3): there is a canonical map `π^*ℳ₀ ⟶ ℳ̃`. -/
@[stacks 01O7] #check
  AlgebraicGeometry.RelativeProjTwistPresentation.degreeZeroToAssociated

/- Lemma 27.17.1 (4): the construction `M ↦ M̃` is a functor. -/
@[stacks 01O7] #check
  AlgebraicGeometry.RelativeProjTwistPresentation.associated

/- Lemma 27.17.1 (5): the associated-sheaf functor is exact. -/
@[stacks 01O7] #check
  AlgebraicGeometry.RelativeProjTwistPresentation.associatedExact

/- Lemma 27.17.1 (6): associated sheaves carry the canonical tensor comparison. -/
@[stacks 01O7] #check
  AlgebraicGeometry.RelativeProjTwistPresentation.associatedTensor

/- Lemma 27.17.1 (7): there is a canonical map to the direct sum of associated shifts. -/
@[stacks 01O7] #check
  AlgebraicGeometry.RelativeProjTwistPresentation.gradedToAssociatedShifts

/- Lemma 27.17.1 (8): formation of the associated sheaf commutes with base change. -/
@[stacks 01O7] #check
  AlgebraicGeometry.RelativeProjTwistPresentation.associatedBaseChangeIso
