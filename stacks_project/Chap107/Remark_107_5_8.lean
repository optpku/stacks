/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeDimension
import StacksCheckRecall

/-!
# Well-definedness of relative dimension of algebraic stacks

The quantity `dimensionAt` of a field-valued 2-fibre of a locally of finite
type morphism of locally Noetherian algebraic stacks is independent of the
chosen field-valued representative of the image point, bilimit cone, and lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Remark 107.5.8: every computation of the dimension at a lift of `t` to a
field-valued bilimit fibre equals `relativeDimensionAt f t`. Hence any two
computations agree, independently of the field-valued representative, bilimit
cone, and lift. -/
@[stacks 0DRM] #check (AlgebraicGeometry.AlgebraicStack.relativeDimensionAt_eq :
    ∀ {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    (f : T ⟶ X) [LocallyOfFiniteType f] (t : Points T)
    (p : FieldValuedPoint X) (hp : Points.mk p = Points.map f t)
    (c : PseudoPullbackCone f p.hom) [AlgebraicStack c.pt]
    [IsLocallyNoetherian c.pt] (hc : c.IsBilimit) (tFiber : Points c.pt)
    (ht : Points.map c.fst tFiber = t),
    relativeDimensionAt f t = dimensionAt tFiber)

end AlgebraicGeometry.AlgebraicStack
