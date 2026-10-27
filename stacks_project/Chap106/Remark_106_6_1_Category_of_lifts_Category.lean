/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Category
import StacksCheckRecall

/-!
# The projection from the category of lifts
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack

universe u

#check (AlgebraicGeometry.AlgebraicStack.Lift.p :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack X']
    (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x],
    AlgebraicGeometry.AlgebraicStack.Lift.Object iX x ⥤ AlgebraicSpace.spacesEtaleSite W)
