module

public import stacks_project.Chap101.Definition_101_14_2_UniversallyInjective

/-!
# Base change of universally injective morphisms of algebraic stacks

Universally injective morphisms of algebraic stacks remain universally
injective along the second projection of any bilimit 2-fibre product cone,
and along the first projection of a chosen 2-fibre product when that leg is
universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.UniversallyInjective

/-- Universally injective morphisms of algebraic stacks remain universally
injective along the second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [UniversallyInjective f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    UniversallyInjective c.snd :=
  sorry

/-- The first projection of a chosen 2-fibre product is universally injective
whenever the second leg is a universally injective morphism of algebraic
stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyInjective g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    UniversallyInjective (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.UniversallyInjective
