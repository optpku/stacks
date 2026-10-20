module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Localization
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- 66.27.0.3: an étale morphism `f : ofOver U ⟶ Y` from a scheme identifies its
small étale site with the localization of the small étale site of `Y` at
`SmallEtale.localizationObject f`. The canonical localization functor is an equivalence,
and the source topology equals the topology induced from the slice topology. -/
@[stacks 04M0] #check
  (AlgebraicGeometry.AlgebraicSpace.SmallEtale.localizationFunctor_isEquivalence :
    ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S} {U : Over S} (f : ofOver U ⟶ Y) [Etale f],
      (SmallEtale.localizationFunctor f).IsEquivalence)

#check
  (AlgebraicGeometry.AlgebraicSpace.SmallEtale.localizationTopology_eq :
    ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S} {U : Over S} (f : ofOver U ⟶ Y) [Etale f],
      SmallEtale.topology (ofOver U) =
        (SmallEtale.localizationFunctor f).inducedTopology
          ((SmallEtale.topology Y).over (SmallEtale.localizationObject f)))
