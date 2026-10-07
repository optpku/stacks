module

public import stacks_project.Chap101.Lemma_101_39_8_Uniqueness
import StacksCheckRecall

@[expose] public section

/- Definition 101.39.6: a morphism `f : X ⟶ Y` of algebraic stacks satisfies the
uniqueness part of the valuative criterion if, for every solid valuative square
`ValuativeCommSq f` and 2-cell `γ` as in Definition 101.39.1, the category of
dotted arrows is either empty or a setoid with exactly one isomorphism class. -/
@[stacks 0CLG] #check AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness
