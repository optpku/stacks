module

public import stacks_project.Chap100.Definition_100_7_2_SmoothLocal
import StacksCheckRecall

@[expose] public section

/- Definition 100.7.2: let `X` be an algebraic stack. Let `P` be a property of
schemes which is local in the smooth topology. We say `X` has property `P` if
any of the equivalent conditions of Lemma 100.7.1 hold. -/
@[stacks 04YG] #check AlgebraicGeometry.AlgebraicStack.hasSmoothLocal
