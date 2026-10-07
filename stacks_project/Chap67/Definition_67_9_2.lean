module

public import stacks_project.Chap67.Definition_67_9_2_Closed
import StacksCheckRecall

@[expose]
public section

/- Definition 67.9.2 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is closed if the map of topological spaces `|X| ⟶ |Y|` is closed. -/
@[stacks 03HI] #check AlgebraicGeometry.AlgebraicSpace.Closed

/- Definition 67.9.2 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is universally closed if for every morphism `Z ⟶ Y` of algebraic spaces the map
`|Z ×_Y X| ⟶ |Z|` is closed, i.e. the base change `Z ×_Y X ⟶ Z` is closed. -/
@[stacks 03HI] #check AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
