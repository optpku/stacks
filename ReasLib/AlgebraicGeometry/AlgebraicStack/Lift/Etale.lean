/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Category

/-!
# Étaleness of compatible morphisms of lifts
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift
namespace Object
namespace Hom

variable {S : Scheme.{u}} {X X' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X']
variable {iX : X ⟶ X'} [IsThickening iX]
variable {W : AlgebraicSpace S} {x : W.toGroupoids ⟶ X}
variable [Groupoids.Hom.Smooth x]

/-- The map between the thickened algebraic spaces of a compatible morphism
of smooth cartesian lifts along a thickening of algebraic stacks is étale. -/
instance etale {ξ η : Object iX x} (φ : Hom ξ η) : AlgebraicSpace.Etale φ.f' := sorry

end Hom
end Object
end AlgebraicGeometry.AlgebraicStack.Lift
