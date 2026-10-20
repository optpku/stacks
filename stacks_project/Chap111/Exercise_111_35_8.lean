module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.InseparablePowerMap

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

/- Exercise 111.35.8 (1): the relative tangent space of
`Spec (𝔽_p(t)) ⟶ Spec (𝔽_p(t^p))` has dimension one at its unique point. -/
@[stacks 029J] #check (AlgebraicGeometry.InseparablePowerMap.tangentDimension_eq_one :
  ∀ (p : ℕ) [Fact p.Prime],
    tangentDimensionAt (AlgebraicGeometry.InseparablePowerMap.hom p) default = 1)

/- Exercise 111.35.8 (2): the relative tangent space of the morphism
`Spec (𝔽_p[t]) ⟶ Spec (𝔽_p[t^p])` has dimension one at every point. -/
@[stacks 029J] #check (AlgebraicGeometry.InseparablePowerMap.affineLine_tangentDimension_eq_one :
  ∀ (p : ℕ) [Fact p.Prime]
    (x : AlgebraicGeometry.InseparablePowerMap.affineLine p),
    tangentDimensionAt (AlgebraicGeometry.InseparablePowerMap.affineLineHom p) x = 1)
