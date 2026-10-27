/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Etale
import StacksCheckRecall

/-!
# Morphisms of lifts are étale on the thickened space
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

/- Lemma 106.6.2: for any morphism of lifts as in diagram 106.6.1.2, the map
`f' : V' ⟶ U'` is étale. Identifying the source lift `ξ` with the `V`-lift and
the target lift `η` with the `U`-lift, Lean `Hom` matches the displayed diagram
(`φ.f' : ξ.U' ⟶ η.U'`) rather than the remark's swapped prose labels. -/
@[stacks 0CJS]
#check (AlgebraicGeometry.AlgebraicStack.Lift.Object.Hom.etale :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack X']
    {iX : X ⟶ X'} [IsThickening iX] {W : AlgebraicSpace S}
    {x : W.toGroupoids ⟶ X} [Groupoids.Hom.Smooth x]
    {ξ η : Object iX x} (φ : Object.Hom ξ η), AlgebraicSpace.Etale φ.f')

end AlgebraicGeometry.AlgebraicStack.Lift
