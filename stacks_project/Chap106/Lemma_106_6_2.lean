/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Remark_106_6_1_Category_of_lifts_Category

/-!
# Morphisms of lifts are étale on the thickened space
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

/-- Lemma 106.6.2: for any morphism of lifts as in diagram 106.6.1.2, the map
`f' : V' ⟶ U'` is étale. Identifying the source lift `ξ` with the `V`-lift and
the target lift `η` with the `U`-lift, Lean `Hom` matches the displayed diagram
(`φ.f' : ξ.U' ⟶ η.U'`) rather than the remark's swapped prose labels. -/
@[stacks 0CJS]
instance etale {ξ η : Object iX x} (φ : Hom ξ η) : AlgebraicSpace.Etale φ.f' := sorry

end Hom
end Object
end AlgebraicGeometry.AlgebraicStack.Lift
