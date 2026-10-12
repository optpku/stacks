/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.QuotientByIdeal.Mapped
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Quotient
public import ReasLib.RingTheory.Ideal.AssociatedPrime.ZeroDivisor
public import ReasLib.RingTheory.Localization.PrimeAvoidance
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization at regular elements of a closed-fiber module

This file describes the prime and maximal spectra obtained by localizing a ring at the
elements acting regularly on a finite module over its Noetherian closed fiber.
-/

@[expose] public section

universe u v w

namespace Module.ClosedFiberLocalization

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
variable [AddCommGroup N] [Module S N]
variable [IsNoetherianRing
  (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))]
variable [Module.Finite
  (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
  (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
    (⊤ : Submodule S N)))]

/-- The primes obtained by contraction from the regular-element localization are exactly
the primes of `S` contained in an associated prime of the closed-fiber module. -/
@[stacks 05DE]
theorem primeSpectrumRange :
    Set.range (PrimeSpectrum.comap
      (algebraMap S (Localization (nonZeroSMulDivisors S
        (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
          (⊤ : Submodule S N))))))) =
      {q : PrimeSpectrum S | ∃ p ∈ associatedPrimesOfModule S
        (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
          (⊤ : Submodule S N))), q.asIdeal ≤ p} := sorry

/-- Every maximal ideal of the regular-element localization contracts from an associated
prime of the closed-fiber module over the closed-fiber ring. -/
@[stacks 05DE]
theorem existsAssociatedPrimeOfMaximal
    (Q : MaximalSpectrum
      (Localization (nonZeroSMulDivisors S
        (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
          (⊤ : Submodule S N)))))) :
    ∃ pbar ∈ associatedPrimesOfModule
        (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
        (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
          (⊤ : Submodule S N))),
      Ideal.comap
          (Ideal.Quotient.mk
            (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))) pbar =
        Ideal.comap
          (algebraMap S (Localization (nonZeroSMulDivisors S
            (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
              (⊤ : Submodule S N)))))) Q.asIdeal := sorry

/-- Localizing at the elements acting regularly on the closed-fiber module gives a semilocal
ring. -/
@[stacks 05DE]
instance instFiniteMaximalSpectrum :
    Finite (MaximalSpectrum
      (Localization (nonZeroSMulDivisors S
        (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
          (⊤ : Submodule S N)))))) := sorry

end Module.ClosedFiberLocalization
