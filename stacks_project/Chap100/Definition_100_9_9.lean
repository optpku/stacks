module

public import stacks_project.Chap100.Lemma_100_9_10_Substack
import StacksCheckRecall

@[expose] public section

/- Definition 100.9.9 (1): an open substack of an algebraic stack `X` is a
strictly full subcategory `X' ⊂ X` such that `X'` is an algebraic stack and
`X' ⟶ X` is an open immersion. -/
@[stacks 04YM] #check AlgebraicGeometry.AlgebraicStack.OpenSubstack

/- Definition 100.9.9 (2): a closed substack of an algebraic stack `X` is a
strictly full subcategory `X' ⊂ X` such that `X'` is an algebraic stack and
`X' ⟶ X` is a closed immersion. -/
@[stacks 04YM] #check AlgebraicGeometry.AlgebraicStack.ClosedSubstack

/- Definition 100.9.9 (3): a locally closed substack of an algebraic stack `X`
is a strictly full subcategory `X' ⊂ X` such that `X'` is an algebraic stack
and `X' ⟶ X` is an immersion. -/
@[stacks 04YM] #check AlgebraicGeometry.AlgebraicStack.LocallyClosedSubstack
