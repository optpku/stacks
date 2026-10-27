/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Fibered

/-!
# The category of lifts is fibred in groupoids
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u

/- Lemma 106.6.3: the projection from the category of lifts constructed in
Remark 106.6.1 to the spaces-étale site is fibred in groupoids. -/
@[stacks 0CJT] #check
  (AlgebraicGeometry.AlgebraicStack.Lift.instIsFiberedInGroupoids :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
      {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x],
      Functor.IsFibered.InGroupoids (AlgebraicGeometry.AlgebraicStack.Lift.p iX x))
