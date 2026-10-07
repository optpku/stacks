module

public import stacks_project.Chap101.Definition_101_12_2_Submersive

/-!
# Base change of universally submersive morphisms of algebraic stacks

Universally submersive morphisms of algebraic stacks remain universally
submersive along the second projection of any bilimit 2-fibre product cone,
and along the first projection of a chosen 2-fibre product when that leg is
universally submersive.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.UniversallySubmersive

/-- Universally submersive morphisms of algebraic stacks remain universally
submersive along the second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [UniversallySubmersive f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    UniversallySubmersive c.snd :=
  sorry

/-- The first projection of a chosen 2-fibre product is universally submersive
whenever the second leg is a universally submersive morphism of algebraic
stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallySubmersive g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    UniversallySubmersive (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.UniversallySubmersive
