/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Stack
import StacksCheckRecall

/-!
# The category of lifts is a stack in groupoids
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u

/- Lemma 106.6.4: the category of lifts is a stack in groupoids. -/
@[stacks 0CJU] #check (AlgebraicGeometry.AlgebraicStack.Lift.instIsStackInGroupoids :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack X']
    (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x],
    IsStack.InGroupoids (AlgebraicSpace.spacesEtaleTopology W)
      (AlgebraicGeometry.AlgebraicStack.Lift.p iX x))
