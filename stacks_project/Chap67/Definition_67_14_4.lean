module

public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject
public import stacks_project.Chap67.Definition_67_14_4_Subscheme
import StacksCheckRecall

@[expose]
public section

/- Definition 67.14.4 (1): the scheme-theoretic intersection of closed subspaces
of an algebraic space `X` corresponding to quasi-coherent ideal sheaves `I` and
`J` is the closed subspace of `X` cut out by `I ⊔ J`. -/
@[stacks 0CYZ] #check AlgebraicGeometry.AlgebraicSpace.schemeTheoreticIntersection

#check AlgebraicGeometry.AlgebraicSpace.schemeTheoreticIntersection_eq_subscheme_sup

/- Definition 67.14.4 (2): the scheme-theoretic union of closed subspaces of an
algebraic space `X` corresponding to quasi-coherent ideal sheaves `I` and `J` is
the closed subspace of `X` cut out by `I ⊓ J`. -/
@[stacks 0CYZ] #check AlgebraicGeometry.AlgebraicSpace.schemeTheoreticUnion

#check AlgebraicGeometry.AlgebraicSpace.schemeTheoreticUnion_eq_subscheme_inf
