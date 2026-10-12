/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_39_7_BaseChange

/-!
# Base change of uniqueness for morphisms of algebraic stacks

The base change of a morphism of algebraic stacks which satisfies the
uniqueness part of the valuative criterion by any morphism of algebraic
stacks again satisfies uniqueness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
namespace Uniqueness

/-- Lemma 101.39.7: The base change of a morphism of algebraic stacks which
satisfies the uniqueness part of the valuative criterion by any morphism of
algebraic stacks is a morphism of algebraic stacks which satisfies the
uniqueness part of the valuative criterion.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g` of a uniqueness morphism `f : X ⟶ Y` along a test
morphism `g : Z ⟶ Y`. -/
@[stacks 0CLH]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Uniqueness f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Uniqueness (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end Uniqueness
end AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
