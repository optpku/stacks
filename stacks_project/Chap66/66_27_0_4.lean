module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Localization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- 66.27.0.4: if `f : X ⟶ Y` is étale between algebraic spaces and `X` is a scheme, then
`X` is an object of `Y_étale` and the small étale ringed sites are identified
`(X_étale, 𝒪_X) = (Y_étale / X, 𝒪_Y |_{Y_étale / X})`. -/
@[stacks 04M1] #check
  (AlgebraicGeometry.AlgebraicSpace.SmallEtale.ringedLocalization :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {Y : AlgebraicGeometry.AlgebraicSpace S}
      {U : CategoryTheory.Over S} (f : AlgebraicGeometry.AlgebraicSpace.ofOver U ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.Etale f],
      (AlgebraicGeometry.AlgebraicSpace.SmallEtale.localizationFunctor f).IsEquivalence ∧
        AlgebraicGeometry.AlgebraicSpace.SmallEtale.topology
            (AlgebraicGeometry.AlgebraicSpace.ofOver U) =
          (AlgebraicGeometry.AlgebraicSpace.SmallEtale.localizationFunctor f).inducedTopology
            ((AlgebraicGeometry.AlgebraicSpace.SmallEtale.topology Y).over
              (AlgebraicGeometry.AlgebraicSpace.SmallEtale.localizationObject f)) ∧
        CategoryTheory.IsIso
          (AlgebraicGeometry.AlgebraicSpace.SmallEtale.localizationStructureSheafMap f))

