/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Defs

@[expose] public section

universe u

open PrimeSpectrum

namespace IsLocalization

variable {A SA TA : Type u} [CommRing A] [CommRing SA] [CommRing TA]
variable [Algebra A SA] [Algebra A TA]

/-- For nested multiplicative subsets, equality of the primes disjoint from them
is equivalent to invertibility of the larger subset in the localization at the smaller one. -/
theorem primeSpectrum_eq_iff_algebraMap_isUnit (S T : Submonoid A)
    [IsLocalization S SA] (hST : S ≤ T) :
    {q : PrimeSpectrum A | Disjoint (S : Set A) q.asIdeal} =
        {q : PrimeSpectrum A | Disjoint (T : Set A) q.asIdeal} ↔
      ∀ t : T, IsUnit (algebraMap A SA (t : A)) := sorry

/-- If nested multiplicative subsets of a commutative ring disjoint from the same
primes, the canonical map between their localizations is bijective. -/
theorem map_bijective_of_primeSpectrum_eq (S T : Submonoid A)
    [IsLocalization S SA] [IsLocalization T TA] (hST : S ≤ T)
    (h_primes :
      {q : PrimeSpectrum A | Disjoint (S : Set A) q.asIdeal} =
        {q : PrimeSpectrum A | Disjoint (T : Set A) q.asIdeal}) :
    Function.Bijective (map TA (RingHom.id A) hST : SA →+* TA) := sorry

end IsLocalization
