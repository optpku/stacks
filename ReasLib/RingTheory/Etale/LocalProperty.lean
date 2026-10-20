module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Invariant properties of commutative local rings

Local-ring properties may respect ring isomorphisms and be invariant at corresponding
primes of étale algebras.
-/

@[expose] public section

universe u

namespace LocalRingProperty

/-- A property of commutative local rings respects isomorphisms when ring equivalences
preserve and reflect the property. -/
def RespectsIso
    (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop) : Prop :=
  ∀ {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S],
    (R ≃+* S) → (P R ↔ P S)

/-- A property of local rings is étale-local at corresponding primes when it is invariant
under étale ring maps: for `Algebra.Etale A B` and `q : PrimeSpectrum B`, `P` holds at
`Localization.AtPrime (q.asIdeal.under A)` if and only if it holds at
`Localization.AtPrime q.asIdeal`. -/
def IsEtaleLocalAtPrimes
    (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop) : Prop :=
  ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : PrimeSpectrum B),
    P (Localization.AtPrime (q.asIdeal.under A)) ↔
      P (Localization.AtPrime q.asIdeal)

/-- Explicit unfolding of étale-invariance of a local-ring property at corresponding primes. -/
theorem isEtaleLocalAtPrimes_iff
    (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop) :
    IsEtaleLocalAtPrimes P ↔
      ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
        (q : PrimeSpectrum B),
        P (Localization.AtPrime (q.asIdeal.under A)) ↔
          P (Localization.AtPrime q.asIdeal) :=
  Iff.rfl

namespace IsEtaleLocalAtPrimes

/-- Transport a local-ring property along the prime localizations of an étale algebra. -/
theorem iff_of {P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop}
    (hP : IsEtaleLocalAtPrimes P) {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B] (q : PrimeSpectrum B) :
    P (Localization.AtPrime (q.asIdeal.under A)) ↔
      P (Localization.AtPrime q.asIdeal) :=
  hP q

end IsEtaleLocalAtPrimes

end LocalRingProperty
