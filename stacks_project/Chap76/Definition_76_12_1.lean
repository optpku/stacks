module

public import stacks_project.Chap76.Definition_76_12_1_Neighbourhood
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 76.12.1: if `i : Z ⟶ X` is an immersion of algebraic spaces, then
its `n`th infinitesimal neighbourhood is the closed subspace of the coborder
open cut out by the `(n + 1)`st power of the coborder kernel ideal. The case
`n = 1` is the first-order infinitesimal neighbourhood, and `fromSource i n` is
the `n`th-order thickening of `Z` over `X`. -/
@[stacks 05ZV] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.space :
    {S : AlgebraicGeometry.Scheme.{u}} →
      {Z X : AlgebraicGeometry.AlgebraicSpace S} → (i : Z ⟶ X) →
        [AlgebraicGeometry.AlgebraicSpace.IsImmersion i] → ℕ →
          AlgebraicGeometry.AlgebraicSpace S)
