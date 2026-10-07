module

public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen
import StacksCheckRecall

@[expose]
public section

/- Definition 67.6.2 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is open if the map of topological spaces `|X| ⟶ |Y|` is open. -/
@[stacks 03Z2] #check AlgebraicGeometry.AlgebraicSpace.Open

/- Definition 67.6.2 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is universally open if for every morphism `Z ⟶ Y` of algebraic spaces the map
`|Z ×_Y X| ⟶ |Z|` is open, i.e. the base change `Z ×_Y X ⟶ Z` is open. -/
@[stacks 03Z2] #check AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
