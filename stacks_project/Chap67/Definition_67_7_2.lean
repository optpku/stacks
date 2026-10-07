module

public import stacks_project.Chap67.Definition_67_7_2_Submersive
import StacksCheckRecall

@[expose]
public section

/- Definition 67.7.2 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is submersive if the continuous map `|X| ⟶ |Y|` is a quotient map. -/
@[stacks 0412] #check AlgebraicGeometry.AlgebraicSpace.Submersive

/- Definition 67.7.2 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is universally submersive if for every morphism `Y' ⟶ Y` of algebraic spaces
the base change `Y' ×_Y X ⟶ Y'` is submersive. -/
@[stacks 0412] #check AlgebraicGeometry.AlgebraicSpace.UniversallySubmersive
