module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
import StacksCheckRecall

@[expose] public section

/- Definition 67.5.2: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is
surjective if the map of associated topological spaces `Points.map f : |X| ⟶ |Y|` is
surjective. -/
@[stacks 03ME] #check AlgebraicGeometry.AlgebraicSpace.Surjective
