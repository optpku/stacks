module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

universe u

namespace Ideal.LocalCohomology

/-- The local-cohomological dimension of a finitely generated ideal is greatest
among the dimensions of its extensions to all prime localizations, with `-1`
as the empty-spectrum baseline. -/
theorem dimension_isGreatest_atPrime {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) :
    IsGreatest
      (insert (-1) (Set.range (fun p : PrimeSpectrum A ↦
        dimension (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
          (hI.map (algebraMap A (Localization.AtPrime p.asIdeal))))))
      (dimension I hI) := sorry

end Ideal.LocalCohomology
