module

public import stacks_project.Chap87.Lemma_87_37_4_Completion
import StacksCheckRecall

@[expose] public section

/- Definition 87.37.3: Let `S` be a scheme. Let `X` be a formal algebraic space over `S`.
Let `T ⊆ Points (reduction X)` be a closed subset. The formal algebraic space of Lemma 87.37.2
is called the completion of `X` along `T`, and is `completionAlong X T`. -/
@[stacks 0GVS] #check AlgebraicGeometry.FormalAlgebraicSpace.completionAlong
