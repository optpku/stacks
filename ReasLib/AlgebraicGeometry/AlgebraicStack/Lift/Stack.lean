/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Category
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids

/-!
# The stack of lifts along a thickening of algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

/-- The projection from cartesian smooth lifts of a smooth algebraic space along a
thickening of algebraic stacks is a stack in groupoids on the spaces-étale site. -/
@[stacks 0CJU]
instance instIsStackInGroupoids {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
    {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] :
    IsStack.InGroupoids (AlgebraicSpace.spacesEtaleTopology W) (p iX x) := sorry

end AlgebraicGeometry.AlgebraicStack.Lift
