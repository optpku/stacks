module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

namespace PrimeSpectrum

/-- The prime spectrum of the integers is not Hausdorff. -/
theorem notT2SpaceInt : ¬ T2Space (PrimeSpectrum ℤ) := sorry

end PrimeSpectrum
