/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Lemma_106_3_7_Diagonal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.AlgebraicStack.IsThickening
open scoped Bicategory

universe u

/- Lemma 106.3.7 (1): a morphism of thickenings `(f, f') : (X ⊂ X') ⟶ (Y ⊂ Y')`
of algebraic stacks induces a thickening
`X ×_Y X ⟶ X' ×_{Y'} X'` of the chosen self 2-fibre products. -/
@[stacks 0BPU] #check Hom.selfMap_isThickening

/- Lemma 106.3.7 (2): the canonical square of relative diagonals Δ, Δ' with
left leg `X ⟶ X'` is a 2-fibre-product square. -/
@[stacks 0BPU] #check Hom.diagonalCone.isBilimit
