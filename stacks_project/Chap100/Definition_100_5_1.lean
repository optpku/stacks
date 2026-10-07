module

public import stacks_project.Chap100.Definition_100_5_1_Surjective
import StacksCheckRecall

@[expose] public section

/- Definition 100.5.1: a morphism `f : X ⟶ Y` of algebraic stacks is
surjective if the map of associated topological spaces `Points.map f : |X| ⟶ |Y|`
is surjective. -/
@[stacks 04ZS] #check AlgebraicGeometry.AlgebraicStack.Surjective
