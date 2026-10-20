module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Base change of pointwise stabilizer preservation

In a cartesian square of algebraic stacks, an isomorphism of automorphism
groups at the image of a point remains an isomorphism at that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.automorphismGroup

/-- In a cartesian square of algebraic stacks, if `f` induces an isomorphism
of automorphism groups at the image of `x'` under the first projection, then
the second projection induces an isomorphism of automorphism groups at `x'`. -/
@[stacks 0DUB]
theorem IsIsoAt.of_isBilimit {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : PseudoPullbackCone f g)
    [AlgebraicStack c.pt] (hc : c.IsBilimit) (x' : |c.pt|)
    (hx : IsIsoAt f (Points.map c.fst x')) : IsIsoAt c.snd x' :=
  sorry

end AlgebraicGeometry.AlgebraicStack.automorphismGroup
