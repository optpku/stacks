/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Radical
import StacksCheckRecall

@[expose] public section

/- Exercise 111.6.3: the map `I ↦ V(I)` is the canonical bijection from radical ideals
to closed subsets of the prime spectrum, with inverse given by the vanishing ideal. -/
@[stacks 02D0]
#check (@PrimeSpectrum.radicalIdealEquivClosed :
  (R : Type _) → [CommSemiring R] →
    {ideal : Ideal R // ideal.IsRadical} ≃
      {closedSet : Set (PrimeSpectrum R) // IsClosed closedSet})

/- Companion: every zero locus is closed, so `I ↦ zeroLocus I` lands in closed sets. -/
#check @PrimeSpectrum.isClosed_zeroLocus

/- Companion: the source condition `I = √I` is equivalent to `I.IsRadical`. -/
#check @Ideal.radical_eq_iff

/- Companion: the inverse of `I ↦ V(I)` recovers the radical as
`vanishingIdeal (zeroLocus I)`. -/
#check @PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical

/- Companion: `zeroLocus` and `vanishingIdeal` form an antitone Galois connection. -/
#check @PrimeSpectrum.gc
