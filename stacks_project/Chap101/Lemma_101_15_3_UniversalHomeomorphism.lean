module

public import stacks_project.Chap101.Definition_101_15_2_UniversalHomeomorphism

/-!
# Base change of universal homeomorphisms of algebraic stacks

Universal homeomorphisms of algebraic stacks remain universal homeomorphisms
along the second projection of any bilimit 2-fibre product cone, and along
the first projection of a chosen 2-fibre product when that leg is a
universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism

/-- Universal homeomorphisms of algebraic stacks remain universal
homeomorphisms along the second projection of any bilimit
`PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [UniversalHomeomorphism f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    UniversalHomeomorphism c.snd :=
  sorry

/-- The first projection of a chosen 2-fibre product is a universal
homeomorphism whenever the second leg is a universal homeomorphism of
algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [UniversalHomeomorphism g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    UniversalHomeomorphism (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism
