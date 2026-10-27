/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Gerbe
import StacksCheckRecall

/-!
# The category of lifts is a gerbe
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u

/- Lemma 106.6.7: the projection from the category of cartesian smooth lifts is a gerbe
on the spaces-étale site of `W`. -/
@[stacks 0CJX] #check (AlgebraicGeometry.AlgebraicStack.Lift.instIsGerbe :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack X']
    (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x],
    CategoryTheory.IsGerbe (AlgebraicSpace.spacesEtaleTopology W)
      (AlgebraicGeometry.AlgebraicStack.Lift.p iX x))
