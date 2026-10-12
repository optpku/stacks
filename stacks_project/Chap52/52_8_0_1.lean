/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Spectrum.Prime.AssociatedSubset

@[expose] public section

universe u

/- 52.8.0.1: For ideals `I` and `J` of a Noetherian ring, the associated subset
consists of the primes `p` such that `zeroLocus p.asIdeal ∩ zeroLocus I` is contained in
`zeroLocus J ∩ zeroLocus I`. -/
@[stacks 0EFG] #check (PrimeSpectrum.associatedSubset_eq_setOf :
  {A : Type u} → [CommRing A] → [IsNoetherianRing A] → ∀ (I J : Ideal A),
    PrimeSpectrum.associatedSubset I J =
      {p |
        PrimeSpectrum.zeroLocus p.asIdeal ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)})
