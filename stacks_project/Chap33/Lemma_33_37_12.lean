/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Localization.PrimeAvoidance

@[expose] public section

universe u

#check (PrimeSpectrum.Avoidance.submonoid :
  ∀ {A : Type u} [CommRing A], Finset (PrimeSpectrum A) → Submonoid A)

#check (PrimeSpectrum.Avoidance.mem_submonoid_iff :
  ∀ {A : Type u} [CommRing A] (s : Finset (PrimeSpectrum A)) (a : A),
    a ∈ PrimeSpectrum.Avoidance.submonoid s ↔ ∀ p ∈ s, a ∉ p.asIdeal)

/- Lemma 33.37.12: localizing a ring away from a finite family of prime ideals gives a
semilocal ring whose maximal ideals correspond to the inclusion-maximal members of the family. -/
@[stacks 09N6] #check
  (PrimeSpectrum.Avoidance.finiteMaximalSpectrum_and_bijective_comap :
    ∀ {A : Type u} [CommRing A] (s : Finset (PrimeSpectrum A)),
      Finite (MaximalSpectrum (Localization (PrimeSpectrum.Avoidance.submonoid s))) ∧
        Function.Bijective (PrimeSpectrum.Avoidance.maximalIdealComap s))
