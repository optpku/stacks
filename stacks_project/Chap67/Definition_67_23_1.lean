module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_23_4_LocallyOfFiniteType
import StacksCheckRecall

@[expose]
public section

/- Definition 67.23.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is locally of finite type if the equivalent conditions of Lemma 67.22.1 hold
with `P` equal to locally of finite type. -/
@[stacks 03XF] #check AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType

/- Definition 67.23.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is of finite type at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X`
of `x` has locally-of-finite-type restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 03XF] #check AlgebraicGeometry.AlgebraicSpace.FiniteTypeAt

/- Definition 67.23.1 (3): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is of finite type if it is locally of finite type and quasi-compact. -/
@[stacks 03XF] #check AlgebraicGeometry.AlgebraicSpace.FiniteType
