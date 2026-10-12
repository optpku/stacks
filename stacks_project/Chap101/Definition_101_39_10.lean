/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_39_12_Existence
import StacksCheckRecall

@[expose] public section

/- Definition 101.39.10: a morphism `f : X ⟶ Y` of algebraic stacks satisfies the
existence part of the valuative criterion if, for every solid valuative square
`ValuativeCommSq f` and 2-cell `γ` as in Definition 101.39.1, there exists a field
extension `K'/K` and a valuation ring `A' ⊂ K'` dominating `A` such that the
category of dotted arrows of the induced outer rectangle, with induced 2-cell
`γ' : y' ∘ j' ⟶ f ∘ x'`, is nonempty. -/
@[stacks 0CLK] #check AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence
