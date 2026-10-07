module

public import stacks_project.Chap67.Definition_67_39_1_Etale
import StacksCheckRecall

@[expose] public section

/- Definition 67.39.1: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is étale at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x` has
étale restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 04RH] #check AlgebraicGeometry.AlgebraicSpace.EtaleAt
