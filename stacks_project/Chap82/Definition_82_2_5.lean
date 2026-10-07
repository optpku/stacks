module

public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 82.2.5 (1): In Situation 82.2.1, for any good `X / B` and any
irreducible closed subset `T ⊂ |X|`, the `δ`-dimension of `T` is `δ_{X/B}(ξ)`
where `ξ ∈ T` is the generic point of `T`. -/
@[stacks 0EDX] #check Hom.deltaDimension

/- Definition 82.2.5 (2): If `T ⊂ |X|` is any closed subset, then `dim_δ(T)` is
the supremum of the `δ`-dimensions of the irreducible components of `T`. -/
@[stacks 0EDX] #check Hom.closedSetDeltaDimension

/- Definition 82.2.5 (3): If `Z` is a closed subspace of `X`, then
`dim_δ(Z) = dim_δ(|Z|)`. -/
@[stacks 0EDX] #check Hom.closedSubspaceDeltaDimension
