module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

universe u v

namespace PrimeSpectrum

/-- The map on prime spectra induced by a faithful integral algebra is surjective. -/
theorem comap_surjective_of_integral (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] :
    Function.Surjective (comap (algebraMap R S)) :=
  Algebra.IsIntegral.comap_surjective R S

end PrimeSpectrum
