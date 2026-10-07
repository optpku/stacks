module

public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap68.Definition_68_22_1_Birational
import StacksCheckRecall

@[expose] public section

/- Definition 68.22.1: Let `S` be a scheme. Let `X` and `Y` be algebraic spaces over `S`.
Assume `X` and `Y` are decent and that `|X|` and `|Y|` have finitely many irreducible
components. A morphism `f : X ⟶ Y` is birational if `|f|` induces a bijection between
the generic points of irreducible components of `|X|` and those of `|Y|`, and for every
generic point `x` of an irreducible component of `|X|` the local ring map
`𝒪_{Y, f(x)} ⟶ 𝒪_{X, x}` is an isomorphism. -/
@[stacks 0ACV] #check AlgebraicGeometry.AlgebraicSpace.IsBirational
#check AlgebraicGeometry.AlgebraicSpace.isBirational_iff
