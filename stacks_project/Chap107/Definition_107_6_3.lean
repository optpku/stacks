module

public import stacks_project.Chap107.Definition_107_6_3_LocalRingDim
import StacksCheckRecall

@[expose]
public section

open AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack.IsLocallyNoetherian X]
  (x : AlgebraicStack.Points X) (hx : AlgebraicStack.IsFiniteTypePoint x)

/- Definition 107.6.3: let `X` be a locally Noetherian algebraic stack. Let
`x ∈ |X|` be a finite type point. The dimension of the local ring of `X` at
`x` is the integer `localRingDimAt x hx` such that the equivalent conditions
of Lemma 107.6.2 hold: some, equivalently every, smooth scheme neighbourhood
`(U, u)` of `x` has `2 dim 𝒪_{U, u} - dim 𝒪_{R, e(u)} = localRingDimAt x hx`. -/
@[stacks 0DSA] #check (AlgebraicGeometry.AlgebraicStack.localRingDimAt x hx : EInt)
