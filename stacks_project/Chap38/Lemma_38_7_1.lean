/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.ClosedFiber
import StacksCheckRecall

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

/- Lemma 38.7.1 (1): localizing `S` at the elements acting regularly on the closed-fiber
module gives a semilocal ring. -/
@[stacks 05DE]
#check
  (Module.ClosedFiberLocalization.instFiniteMaximalSpectrum :
      Finite (MaximalSpectrum
        (Localization (nonZeroSMulDivisors S
          (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
            (⊤ : Submodule S N)))))))

/- Lemma 38.7.1 (2): the primes obtained by contraction from the localization are exactly
the primes of `S` contained in an associated prime of the closed-fiber module. -/
@[stacks 05DE]
#check
  (Module.ClosedFiberLocalization.primeSpectrumRange :
      Set.range (PrimeSpectrum.comap
        (algebraMap S (Localization (nonZeroSMulDivisors S
          (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
            (⊤ : Submodule S N))))))) =
        {q : PrimeSpectrum S | ∃ p ∈ associatedPrimesOfModule S
          (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
            (⊤ : Submodule S N))), q.asIdeal ≤ p})

/- Lemma 38.7.1 (3): every maximal ideal of the regular-element localization contracts
from an associated prime of the closed-fiber module over the closed-fiber ring. -/
@[stacks 05DE]
#check
  (Module.ClosedFiberLocalization.existsAssociatedPrimeOfMaximal :
      ∀ Q : MaximalSpectrum
        (Localization (nonZeroSMulDivisors S
          (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
            (⊤ : Submodule S N))))),
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
                (⊤ : Submodule S N)))))) Q.asIdeal)

end Module.ClosedFiberLocalization
