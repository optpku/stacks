module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Separated
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

universe u

/- Lemma 71.11.6. In Situation 71.11.1, the structure morphism of the relative `Proj` is
separated. Its canonical chart presentation is expressed by being étale-locally the scheme
relative `Proj` of a one-and-mul-preserving `Type u` section model of `𝒜`, via the canonical
structure morphism `etaleChartProj`. -/
@[stacks 084E] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.separated :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π), Separated π)
