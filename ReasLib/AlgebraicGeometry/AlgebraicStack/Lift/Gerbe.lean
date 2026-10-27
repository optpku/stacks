/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Category
public import ReasLib.CategoryTheory.Fibered.Gerbe.Basic

/-!
# The gerbe of lifts of algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

/-- For a thickening of algebraic stacks and a smooth morphism from an algebraic space `W`,
the projection from the category of cartesian smooth lifts is a gerbe on the spaces-étale
site of `W`. -/
@[stacks 0CJX]
instance instIsGerbe {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
    {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] :
    CategoryTheory.IsGerbe (AlgebraicSpace.spacesEtaleTopology W) (p iX x) := sorry

end AlgebraicGeometry.AlgebraicStack.Lift
