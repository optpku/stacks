module

import StacksCheckRecall
public import ReasLib.RingTheory.Spectrum.Prime.Compact

@[expose] public section

universe u

/- Exercise 111.6.5: for any ring `A`, `Spec(A)` is quasi-compact. -/
@[stacks 02D1]
#check (PrimeSpectrum.isQuasiCompact :
  ∀ (R : Type u) [CommSemiring R], TopologicalSpace.IsQuasiCompact (PrimeSpectrum R))
