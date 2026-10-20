/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong

open AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace (Points)
open CategoryTheory Limits Opposite TopologicalSpace

universe u

/- Lemma 87.37.4: Completion along a closed subset of a reduction commutes with
pullback along a morphism of formal algebraic spaces over a scheme. -/
@[stacks 0GVT] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.completionAlong_isPullback :
    ∀ {S : Scheme.{u}} {X' X : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X'] [IsFormalAlgebraicSpace X]
      (R' : ReductionData X') (R : ReductionData X) (f : X' ⟶ X)
      (T : Closeds (Points R.space)),
      IsPullback
        (Recompletion.ι R' (T.preimage (Points.continuous_map (R'.map R f))))
        (Recompletion.map R' R f T) f (Recompletion.ι R T))
