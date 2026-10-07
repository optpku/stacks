module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.RegularMeromorphicSection
import StacksCheckRecall

/-!
# Definition 31.23.7

The reusable regular-meromorphic-section API is owned by
`ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.RegularMeromorphicSection`.

@stack 02OX
-/

@[expose] public section

universe u

/- Definition 31.23.7. For a locally ringed space `X`, an invertible `𝒪_X`-module `ℒ`, and a
meromorphic section `s` of `ℒ`, regularity means that the induced map
`𝒦_X ⟶ 𝒦_X(ℒ)` is a monomorphism. The checked predicate is the canonical generalization to an
arbitrary module sheaf. -/
@[stacks 02OX] #check
  (AlgebraicGeometry.LocallyRingedSpace.IsRegularMeromorphicSection :
    (X : AlgebraicGeometry.LocallyRingedSpace.{u}) →
      (ℱ : SheafOfModules.RingedSite.ringedSiteModuleCategory
        (Opens.grothendieckTopology X.toTopCat) X.𝒪) →
        X.meromorphicSections ℱ → Prop)
