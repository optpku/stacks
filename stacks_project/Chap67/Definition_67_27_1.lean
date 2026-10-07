module

public import stacks_project.Chap67.Definition_67_27_1_QuasiFinite
public import stacks_project.Chap67.Lemma_67_27_3_QuasiFinite
import StacksCheckRecall

@[expose] public section

/- Definition 67.27.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is locally quasi-finite if the equivalent conditions of Lemma 67.22.1 hold
with `P` equal to locally quasi-finite, i.e. locally of finite type and locally
quasi-finite. -/
@[stacks 03XJ] #check AlgebraicGeometry.AlgebraicSpace.FiniteType.locallyQuasiFinite_iff

/- Definition 67.27.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is quasi-finite at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X`
of `x` has locally quasi-finite restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 03XJ] #check AlgebraicGeometry.AlgebraicSpace.FiniteType.QuasiFiniteAt

/- Definition 67.27.1 (3): a morphism of algebraic spaces `f : X ⟶ Y` is
quasi-finite if it is locally quasi-finite and quasi-compact. -/
@[stacks 03XJ] #check AlgebraicGeometry.AlgebraicSpace.QuasiFinite
