module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Local
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.FiniteLocallyFreeStage
public import ReasLib.RingTheory.Flatness.LocallyFree

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- If every stage of a coherent formal module is finite locally free over its
corresponding ideal-power quotient, then each completed stalk is finite locally
free away from the vanishing locus of the completed ideal. -/
theorem finiteLocallyFreeOutside_of_finiteLocallyFreeStages
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_stage : ∀ n : ℕ, IsFiniteLocallyFreeStage F n) :
    ∀ y : S.Y, (hy : S.y y ∈ S.U) →
      let yU := closedFiberOpenPoint S y hy
      ∀ p : PrimeSpectrum (completedLocalRing S yU),
        p ∉ PrimeSpectrum.zeroLocus
            (completedIdeal S yU : Set (completedLocalRing S yU)) →
          Module.FiniteLocallyFree (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU)) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
