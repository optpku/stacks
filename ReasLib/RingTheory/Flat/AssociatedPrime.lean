/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Topology.Inseparable
public import ReasLib.RingTheory.Ideal.AssociatedPrime.BaseChange.Flat

/-!
# Flatness and associated primes

Criteria relating preservation of nonzerodivisors, flatness after total-quotient-ring base
change, and flatness at associated primes.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace RingHom.Flat

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [IsNoetherianRing B]

/-- Preservation of nonzerodivisors and flatness after base change to the total quotient ring
imply flatness at associated primes of the target and at primes lying over associated primes of
the source. -/
theorem overAssociatedPrimes_of_totalQuotientBaseChange
    (h : nonZeroDivisors A ≤ Submonoid.comap (algebraMap A B) (nonZeroDivisors B) ∧
      (Algebra.TensorProduct.includeLeft :
        FractionRing A →ₐ[A] FractionRing A ⊗[A] B).toRingHom.Flat) :
    (∀ q : PrimeSpectrum B, q.asIdeal ∈ associatedPrimes B B →
      (algebraMap A (Localization.AtPrime q.asIdeal)).Flat) ∧
    (∀ q : PrimeSpectrum B, q.asIdeal.under A ∈ associatedPrimes A A →
      (algebraMap A (Localization.AtPrime q.asIdeal)).Flat) := sorry

/-- Flatness at every associated prime of the target implies that nonzerodivisors of the source
map to nonzerodivisors of the target. -/
theorem preservesNonZeroDivisors_of_atAssociatedPrimes
    (h : ∀ q : PrimeSpectrum B, q.asIdeal ∈ associatedPrimes B B →
      (algebraMap A (Localization.AtPrime q.asIdeal)).Flat) :
    nonZeroDivisors A ≤ Submonoid.comap (algebraMap A B) (nonZeroDivisors B) := sorry

/-- If going up holds, preservation of nonzerodivisors together with total-quotient-ring
base-change flatness is equivalent to flatness at associated primes of the target and at primes
lying over associated primes of the source. -/
theorem totalQuotientBaseChange_iff_overAssociatedPrimes_of_goingUp
    (h_goingUp : SpecializingMap (PrimeSpectrum.comap (algebraMap A B))) :
    (nonZeroDivisors A ≤ Submonoid.comap (algebraMap A B) (nonZeroDivisors B) ∧
      (Algebra.TensorProduct.includeLeft :
        FractionRing A →ₐ[A] FractionRing A ⊗[A] B).toRingHom.Flat) ↔
    (∀ q : PrimeSpectrum B, q.asIdeal ∈ associatedPrimes B B →
        (algebraMap A (Localization.AtPrime q.asIdeal)).Flat) ∧
      (∀ q : PrimeSpectrum B, q.asIdeal.under A ∈ associatedPrimes A A →
        (algebraMap A (Localization.AtPrime q.asIdeal)).Flat) := sorry

end RingHom.Flat
