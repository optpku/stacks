/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Lemma_106_3_5_Composition
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 106.3.5: if `X ⊂ X'` and `X' ⊂ X''` are thickenings of algebraic stacks,
then the composite inclusion `X ⊂ X''` is a thickening, recovered as the
composite 1-morphism `f ≫ g`. -/
@[stacks 0BPS] #check
  (IsThickening.comp : ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsThickening f] [IsThickening g],
    IsThickening (f ≫ g))
