module

public import stacks_project.Chap106.Definition_106_3_3_FirstOrderThickening
import StacksCheckRecall

@[expose] public section

/- Definition 106.3.3: an algebraic stack `X'` is a first-order thickening of an
algebraic stack `X` if `X` is a closed substack of `X'` and `X ⟶ X'` is a
first-order thickening in the sense of Properties of Stacks, Section 100.3. -/
@[stacks 0BPQ] #check AlgebraicGeometry.AlgebraicStack.IsFirstOrderThickening
