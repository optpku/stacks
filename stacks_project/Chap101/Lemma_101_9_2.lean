/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_9_2_BaseChange

/-!
# Base change of affine morphisms of algebraic stacks

The base change of an affine morphism of algebraic stacks by any morphism of
algebraic stacks is affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom
namespace Affine

/-- Lemma 101.9.2: Let `X ⟶ Y` be a morphism of algebraic stacks. Let
`Z ⟶ Y` be an affine morphism of algebraic stacks. Then
`Z ×_Y X ⟶ X` is an affine morphism of algebraic stacks.

Stacks writes the base change as `Z ×_Y X ⟶ X`; the Lean projection is
`TwoFibreProduct.snd f g` of an affine `f` along a test morphism `g`. -/
@[stacks 0CHR]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Affine f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Affine (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end Affine
end AlgebraicGeometry.Groupoids.Hom
