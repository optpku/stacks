module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicSpace

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X)

/- Definition 66.9.1: for a scheme `S`, an algebraic space `X` over `S`, and a point
`x ∈ |X|`, the dimension `dimensionAt x` is the étale-local dimension of `X` at `x`,
equal to `topologicalKrullDimAt u` for any (equivalently some) étale morphism
`a : ofOver U ⟶ X` from a scheme with `Points.mapOfOver a u = x`. This is not the
local topological dimension of `Points X`. -/
@[stacks 04N5] #check (AlgebraicGeometry.AlgebraicSpace.dimensionAt x : WithBot ℕ∞)
