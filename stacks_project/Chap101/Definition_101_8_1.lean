module

public import stacks_project.Chap101.Definition_101_8_1_Noetherian
import StacksCheckRecall

@[expose] public section

/- Definition 101.8.1: an algebraic stack `X` is Noetherian if it is
quasi-compact, quasi-separated and locally Noetherian. -/
@[stacks 0510] #check AlgebraicGeometry.AlgebraicStack.IsNoetherian
