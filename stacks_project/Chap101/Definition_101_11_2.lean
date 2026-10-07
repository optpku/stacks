module

public import stacks_project.Chap101.Lemma_101_11_3_UniversallyOpen
import StacksCheckRecall

@[expose] public section

/- Definition 101.11.2 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
open if the map of topological spaces `|X| ⟶ |Y|` is open. -/
@[stacks 06U2] #check AlgebraicGeometry.AlgebraicStack.Open

/- Definition 101.11.2 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
universally open if for every morphism of algebraic stacks `Z ⟶ Y` the map
`|Z ×_Y X| ⟶ |Z|` is open, i.e. the base change `Z ×_Y X ⟶ Z` is open. -/
@[stacks 06U2] #check AlgebraicGeometry.AlgebraicStack.UniversallyOpen
