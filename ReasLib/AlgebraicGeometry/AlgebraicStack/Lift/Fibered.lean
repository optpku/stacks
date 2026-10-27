/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Category
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# The category of lifts is fibred in groupoids
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

/-- The projection from smooth cartesian lifts across a thickening of algebraic stacks
to the spaces-étale site of the original algebraic space is fibred in groupoids. -/
@[stacks 0CJT]
instance instIsFiberedInGroupoids {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
    {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] :
    Functor.IsFibered.InGroupoids (p iX x) := sorry

end AlgebraicGeometry.AlgebraicStack.Lift
