module

public import stacks_project.Chap75.Definition_75_9_1_Square
import StacksCheckRecall

/- Definition 75.9.1. A commutative diagram of algebraic spaces over a scheme `S`
is an elementary distinguished square when `j : U ⟶ W` is an open-subspace
inclusion, `f : V ⟶ W` is étale, and `f⁻¹(T) ⟶ T` is an isomorphism for
`T = W \ U` with the reduced induced subspace structure. -/
@[stacks 08GM] #check AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare
