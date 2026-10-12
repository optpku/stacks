/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_5_3_BaseChange

/-!
# Base change of surjective morphisms of algebraic stacks

The base change of a surjective morphism of algebraic stacks is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Surjective

/-- Lemma 100.5.3: The base change of a surjective morphism of algebraic stacks
is surjective.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; Lean's chosen projection is
`TwoFibreProduct.snd f g` for a surjective morphism `f : X ⟶ Y` along
`g : Z ⟶ Y`. -/
@[stacks 04ZU]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Surjective (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Surjective
