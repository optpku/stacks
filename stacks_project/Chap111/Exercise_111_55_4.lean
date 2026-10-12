/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.PrimeSpectrum
import StacksCheckRecall

@[expose] public section

universe u

open PrimeSpectrum

/- Exercise 111.55.4
For nested multiplicative subsets of a commutative ring, equality of the primes
disjoint from them gives a bijective map between their localizations. -/
@[stacks 07DI] #check (IsLocalization.map_bijective_of_primeSpectrum_eq :
    ∀ {A SA TA : Type u} [CommRing A] [CommRing SA] [CommRing TA]
      [Algebra A SA] [Algebra A TA] (S T : Submonoid A)
      [IsLocalization S SA] [IsLocalization T TA] (hST : S ≤ T),
      ({q : PrimeSpectrum A | Disjoint (S : Set A) q.asIdeal} =
          {q : PrimeSpectrum A | Disjoint (T : Set A) q.asIdeal}) →
        Function.Bijective (IsLocalization.map TA (RingHom.id A) hST : SA →+* TA))
