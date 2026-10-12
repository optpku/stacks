/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Base change of universally closed morphisms of algebraic stacks

Universally closed morphisms of algebraic stacks remain universally closed
along the second projection of any bilimit 2-fibre product cone, and along
the first projection of a chosen 2-fibre product when that leg is
universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.UniversallyClosed

/-- Universally closed morphisms of algebraic stacks remain universally closed
along the second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [UniversallyClosed f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    UniversallyClosed c.snd :=
  sorry

/-- The first projection of a chosen 2-fibre product is universally closed
whenever the second leg is a universally closed morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyClosed g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    UniversallyClosed (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.UniversallyClosed
