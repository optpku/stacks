module

public import stacks_project.Chap87.Lemma_87_14_4_Completion
import StacksCheckRecall

@[expose] public section

/- Definition 87.14.3: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `T ⊆ Points X` be a closed subset. The formal algebraic space of Lemma 87.14.2
is called the completion of `X` along `T`, and is `completionAlong X T`. -/
@[stacks 0AMC] #check AlgebraicGeometry.AlgebraicSpace.completionAlong
