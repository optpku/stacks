module

public import ReasLib.AlgebraicGeometry.WLocalHull.Limit
import StacksCheckRecall

@[expose] public section

universe u

/- 61.5.2.6 (1): the affine scheme `X_w` is a limit of the inverse system
`X_E` of finite-stage spectra, as `E` runs over the directed poset of finite
subsets of `A`. -/
@[stacks 0974] #check (AlgebraicGeometry.WLocal.Construction.isLimit_schemeCone :
  ∀ (A : Type u) [CommRing A],
    CategoryTheory.Limits.IsLimit (AlgebraicGeometry.WLocal.Construction.schemeCone A))

/- 61.5.2.6 (2): the closed subscheme `Z` is a limit of the inverse system
`Z_E` of finite-stage closed subschemes. -/
@[stacks 0974] #check (AlgebraicGeometry.WLocal.Construction.isLimit_closedCone :
  ∀ (A : Type u) [CommRing A],
    CategoryTheory.Limits.IsLimit (AlgebraicGeometry.WLocal.Construction.closedCone A))

/- 61.5.2.6 (3): the inclusion `Z ⟶ X_w` is a closed immersion, so
`X_w ⊃ Z` as a closed subscheme. -/
@[stacks 0974] #check (AlgebraicGeometry.WLocal.Construction.isClosedImmersion_closedι :
  ∀ (A : Type u) [CommRing A],
    AlgebraicGeometry.IsClosedImmersion (AlgebraicGeometry.WLocal.Construction.closedι A))
