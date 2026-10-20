module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism

/-!
# Base change of universal homeomorphisms of algebraic stacks

Universal homeomorphisms of algebraic stacks remain universal homeomorphisms
under arbitrary base change, expressed by bilimit cones or chosen 2-fibre products.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversalHomeomorphism

/-- The second projection of a bilimit 2-fibre-product cone of algebraic stacks
is a universal homeomorphism whenever the first leg is a universal homeomorphism. -/
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
    (f : X ⟶ Y) (g : Z ⟶ Y) [UniversalHomeomorphism g] :
    UniversalHomeomorphism (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end UniversalHomeomorphism

/-- The second projection of a chosen 2-fibre product is a universal
homeomorphism whenever the first leg is a universal homeomorphism of
algebraic stacks. -/
instance universalHomeomorphism_pullback_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [UniversalHomeomorphism f] :
    UniversalHomeomorphism (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
