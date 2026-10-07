module

public import stacks_project.Chap101.Lemma_101_26_1_Square

/-!
# Independence of flatness at a point

For a morphism of algebraic stacks, flatness of the top arrow at a point of an
algebraic-space test square is independent of the choice of square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.26.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks and let
`x` be a point of `Points X`. Among 2-commutative algebraic-space squares
over `f` through a point `u` mapping to `x`, with `b : V.toGroupoids ⟶ Y` flat
and comparison `(a, h) : U ⟶ TwoFibreProduct.apex f b` flat, the top arrow `h`
is flat at `u` for one such diagram if and only if it is flat at `u` for every
such diagram. -/
@[stacks 0CIC]
theorem forallFlatAtPointSquare_iff_existsFlatAtPointSquare
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : Points X) :
    forallFlatAtPointSquare f x ↔ existsFlatAtPointSquare f x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
