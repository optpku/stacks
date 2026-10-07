module

public import stacks_project.Chap100.Definition_100_12_3_Dimension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack.IsLocallyNoetherian X] (x : AlgebraicStack.Points X)

/- Definition 100.12.2: let `X` be a locally Noetherian algebraic stack over a scheme `S`.
Let `x` be a point of `|X|`. For a presentation `P : Presentation X` (Definition 94.16.5)
whose object space is a scheme and a point `u` mapping to `x`, the dimension
`dimensionAt x` of `X` at `x` is the element of `ℤ ∪ {∞}` given by
`dimensionDiff (dimensionAt u) (fiberDimensionAt s (e u))`, equivalently
`Presentation.dimensionDiffAt`, in the notation of Lemma 100.12.1. -/
@[stacks 0AFN] #check (AlgebraicGeometry.AlgebraicStack.dimensionAt x : EInt)
