/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_12_3_UniversallySubmersive

/-!
# Base change of universally submersive morphisms of algebraic stacks

The base change of a universally submersive morphism of algebraic stacks by any
morphism of algebraic stacks is universally submersive.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.12.3: The base change of a universally submersive morphism of
algebraic stacks by any morphism of algebraic stacks is universally submersive.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 0CHY]
instance universallySubmersive_pullback_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallySubmersive f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    UniversallySubmersive (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
