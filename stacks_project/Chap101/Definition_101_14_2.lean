module

public import stacks_project.Chap101.Definition_101_14_2_UniversallyInjective
import StacksCheckRecall

@[expose] public section

/- Definition 101.14.2: a morphism `f : X ⟶ Y` of algebraic stacks is
universally injective if for every morphism of algebraic stacks `Z ⟶ Y` the
map `|Z ×_Y X| ⟶ |Z|` is injective. -/
@[stacks 0CI2] #check AlgebraicGeometry.AlgebraicStack.UniversallyInjective
