module

public import stacks_project.Chap66.Definition_66_25_2_RegularAt
import StacksCheckRecall

@[expose] public section

/- Definition 66.25.2: for a scheme `S`, an algebraic space `X` over `S`, and a point
`x ∈ |X|`, we say `X` is regular at `x` if `𝒪_{U,u}` is a regular local ring for any
(equivalently some) étale morphism `a : U → X` from a scheme with `a(u) = x`. -/
@[stacks 0AH9] #check AlgebraicGeometry.AlgebraicSpace.RegularAt
