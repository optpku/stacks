module

public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicSpace

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X)

/- Definition 66.10.2: for a scheme `S`, an algebraic space `X` over `S`, and a point
`x ∈ |X|`, the dimension of the local ring of `X` at `x` is `localRingDimAt x`, the unique
`d` in `WithBot ℕ∞` satisfying the equivalent conditions of Lemma 66.10.1. In this case
`x` is also a point of codimension `d` on `X`, meaning `localRingDimAt x = d`. -/
@[stacks 04NA] #check (AlgebraicGeometry.AlgebraicSpace.localRingDimAt x : WithBot ℕ∞)
