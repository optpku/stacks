/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong.Reduction
import StacksCheckRecall

/-!
# Reduction of recompletion along a closed subset

The reduction of the completion of a formal algebraic space along a closed
subset of its reduction is the reduced induced closed subspace on that subset.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace (Points ClosedSubspaceStructure)
open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

universe u

/- Lemma 87.37.5: The reduction of the completion of a formal algebraic space
along a closed subset of its reduction is the reduced induced closed subspace
on that subset. -/
@[stacks 0GVU] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.reduction_completionAlong :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
      (R : ReductionData X) (T : Closeds (Points R.space)),
      Recompletion.reductionSpace R T = (ClosedSubspaceStructure.reduced T).space)

#check (AlgebraicGeometry.FormalAlgebraicSpace.reductionι_completionAlong :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    (R : ReductionData X) (T : Closeds (Points R.space)),
    Recompletion.reductionι R T = Recompletion.fromReduced R T)
