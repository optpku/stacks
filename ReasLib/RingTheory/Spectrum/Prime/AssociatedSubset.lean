/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

universe u

namespace PrimeSpectrum

variable {A : Type u} [CommRing A]

/-- The primes whose closed subsets meet `zeroLocus I` only inside
`zeroLocus J ∩ zeroLocus I`. -/
def associatedSubset (I J : Ideal A) : Set (PrimeSpectrum A) :=
  {p |
    zeroLocus p.asIdeal ∩ zeroLocus (I : Set A) ⊆
      zeroLocus (J : Set A) ∩ zeroLocus (I : Set A)}

/-- Membership in `associatedSubset I J` is the corresponding inclusion of zero loci. -/
theorem mem_associatedSubset (I J : Ideal A) (p : PrimeSpectrum A) :
    p ∈ associatedSubset I J ↔
      zeroLocus p.asIdeal ∩ zeroLocus (I : Set A) ⊆
        zeroLocus (J : Set A) ∩ zeroLocus (I : Set A) := sorry

/-- The subset `associatedSubset I J` is stable under specialization. -/
theorem stableUnderSpecialization_associatedSubset (I J : Ideal A) :
    StableUnderSpecialization (associatedSubset I J) := sorry

/-- For ideals `I` and `J` of a Noetherian ring, `associatedSubset I J` is the set of
primes `p` for which `zeroLocus p.asIdeal ∩ zeroLocus I` is contained in
`zeroLocus J ∩ zeroLocus I`. -/
theorem associatedSubset_eq_setOf [IsNoetherianRing A] (I J : Ideal A) :
    associatedSubset I J =
      {p |
        zeroLocus p.asIdeal ∩ zeroLocus (I : Set A) ⊆
          zeroLocus (J : Set A) ∩ zeroLocus (I : Set A)} := sorry

end PrimeSpectrum
