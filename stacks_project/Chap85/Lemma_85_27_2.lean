module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicTopology.SimplicialObject.Descent

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 85.27.2: Cartesian simplicial schemes over `X` are equivalent to pairs
`(V, φ)` over degree zero, with `φ` an isomorphism from the `δ 1` pullback to the
`δ 0` pullback, satisfying the degeneracy identity and the degree-two cocycle. -/
@[stacks 07TC] #check (CategoryTheory.SimplicialObject.cartesianOverEquivalence :
  ∀ (X : SimplicialObject Scheme.{u}),
    CategoryTheory.SimplicialObject.CartesianOver X ≌
      CategoryTheory.SimplicialObject.CartesianDatum X)
