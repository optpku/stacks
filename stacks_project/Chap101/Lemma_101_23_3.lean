/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_23_3_BaseChange

/-!
# Base change of locally quasi-finite morphisms of algebraic stacks

A base change of a locally quasi-finite morphism of algebraic stacks is
locally quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite

/-- Lemma 101.23.3: A base change of a locally quasi-finite morphism is
locally quasi-finite.

Stacks writes the base change as `Y' ×_Y X ⟶ Y'`; the Lean projection is
`TwoFibreProduct.snd f g` of a locally quasi-finite morphism `f : X ⟶ Y`
along a test morphism `g : Z ⟶ Y`. -/
@[stacks 06UB]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyQuasiFinite f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    LocallyQuasiFinite (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
