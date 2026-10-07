module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
import StacksCheckRecall

@[expose] public section

/- Definition 67.37.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is smooth if the equivalent conditions of Lemma 67.22.1 hold with `P` = smooth. -/
@[stacks 03ZC] #check AlgebraicGeometry.AlgebraicSpace.Smooth

/- Definition 67.37.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is smooth at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x` has
smooth restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 03ZC] #check AlgebraicGeometry.AlgebraicSpace.SmoothAt
