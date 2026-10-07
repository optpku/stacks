module

import StacksCheckRecall
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

/- Exercise 111.6.5: for any ring `A`, `Spec(A)` is quasi-compact. Mathlib owns this as the
canonical instance `PrimeSpectrum.compactSpace : CompactSpace (PrimeSpectrum R)`, already for a
commutative semiring. -/
@[stacks 02D1]
#check @PrimeSpectrum.compactSpace
