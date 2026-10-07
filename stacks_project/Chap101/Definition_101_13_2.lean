module

public import stacks_project.Chap101.Definition_101_13_2_Closed
import StacksCheckRecall

@[expose] public section

/- Definition 101.13.2 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
closed if the map of topological spaces `|X| ⟶ |Y|` is closed. -/
@[stacks 0513] #check AlgebraicGeometry.AlgebraicStack.Closed

/- Definition 101.13.2 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
universally closed if for every morphism of algebraic stacks `Z ⟶ Y` the map
`|Z ×_Y X| ⟶ |Z|` is closed, i.e. the base change `Z ×_Y X ⟶ Z` is closed. -/
@[stacks 0513] #check AlgebraicGeometry.AlgebraicStack.UniversallyClosed
