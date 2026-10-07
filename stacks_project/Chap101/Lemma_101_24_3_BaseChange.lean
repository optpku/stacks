module

public import stacks_project.Chap101.Definition_101_24_1_QuasiFinite

/-!
# Base change of quasi-finite morphisms of algebraic stacks

Quasi-finite morphisms of algebraic stacks remain quasi-finite along the
second projection of any bilimit 2-fibre product cone, and along the first
projection of a chosen 2-fibre product when that leg is quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiFinite

/-- Quasi-finite morphisms of algebraic stacks remain quasi-finite along the
second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [QuasiFinite f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    QuasiFinite c.snd := sorry

/-- The first projection of a chosen 2-fibre product is quasi-finite whenever
the second leg is a quasi-finite morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiFinite g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    QuasiFinite (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

end AlgebraicGeometry.AlgebraicStack.QuasiFinite
