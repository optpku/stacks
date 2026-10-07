module

public import stacks_project.Chap101.Definition_101_26_2_FlatAt
import StacksCheckRecall

@[expose] public section

/- Definition 101.26.2: let `f : X ⟶ Y` be a morphism of algebraic stacks
and let `x` be a point of `Points X`. We say `f` is flat at `x` if the
equivalent conditions of Lemma 101.26.1 hold. -/
@[stacks 0CID] #check AlgebraicGeometry.AlgebraicStack.FlatAt
