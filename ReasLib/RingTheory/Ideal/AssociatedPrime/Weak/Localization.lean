/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Local
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Weakly associated primes and localization

This file relates weak association before and after localization, including
contraction and range criteria, invariance under regular denominators, and
tests using the maximal ideal of a prime localization.
-/

universe u v

section

variable {R : Type u} [CommRing R]

namespace weaklyAssociatedPrimes.Localization

/-- An associated prime at the maximal ideal of `Rₚ` descends to a weakly
associated prime of the original `R`-module. -/
@[stacks 0566 "local associated-prime descent"]
theorem mem_of_maximalIdeal_associated
    (p : Ideal R) [p.IsPrime] {X : Type*} [AddCommGroup X] [Module R X]
    (hp :
      IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule.AtPrime p X)) :
    p ∈ weaklyAssociatedPrimes R X := sorry

variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The weakly associated primes of a localized module, contracted to the base
ring, are its weakly associated primes when regarded as a module over the base
ring. -/
@[stacks 05C9 "localized module image under contraction"]
theorem localizedModule_eq_image_comap :
    Ideal.comap (algebraMap R (Localization S)) ''
        weaklyAssociatedPrimes (Localization S) (LocalizedModule S M) =
      weaklyAssociatedPrimes R (LocalizedModule S M) := sorry

/-- The weakly associated primes of a localization are the weakly associated
primes of the original module lying in the range of contraction from the
localized ring. -/
@[stacks 05C9 "localized module range criterion"]
theorem inter_localization_range_eq :
    weaklyAssociatedPrimes R M ∩
        Set.range (Ideal.comap (algebraMap R (Localization S))) =
      weaklyAssociatedPrimes R (LocalizedModule S M) := sorry

/-- Localization at a multiplicative set of module-regular elements does not
change the weakly associated primes over the base ring. -/
@[stacks 05CA "regular-denominator localization equality"]
theorem eq_of_isSMulRegular
    (hS : ∀ s : S, IsSMulRegular M s) :
    weaklyAssociatedPrimes R M =
      weaklyAssociatedPrimes R (LocalizedModule S M) := sorry

end weaklyAssociatedPrimes.Localization

namespace weaklyAssociatedPrimes.Localization

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The product of the localization maps at all weakly associated primes of a
module is injective. -/
@[stacks 05CB "localization product map injectivity"]
theorem localizationMap_injective :
    Function.Injective
      ⇑(LinearMap.pi fun p : weaklyAssociatedPrimes R M ↦
        LocalizedModule.mkLinearMap p.1.primeCompl M) := sorry

end weaklyAssociatedPrimes.Localization

namespace Ideal.IsWeaklyAssociatedToModule.Localization

variable {M : Type v}
variable [AddCommGroup M] [Module R M]
variable (p : Ideal R) [p.IsPrime]

/-- A prime is weakly associated to a module exactly when the maximal ideal of
the prime localization is weakly associated to the localized module. -/
@[stacks 0566 "localization criterion for weak association"]
theorem iff_maximalIdeal :
    Ideal.IsWeaklyAssociatedToModule R M p ↔
      Ideal.IsWeaklyAssociatedToModule (Localization.AtPrime p)
        (LocalizedModule.AtPrime p M)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) := sorry

/-- A prime is weakly associated to a module exactly when the maximal ideal of
the prime localization is an associated prime of the localized module. -/
@[stacks 0566 "localized associated-prime criterion"]
theorem iff_associatedPrime :
    Ideal.IsWeaklyAssociatedToModule R M p ↔
      IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule.AtPrime p M) := sorry

/-- In a prime localization, weak association of the maximal ideal to the
localized module is equivalent to its being an associated prime. -/
@[stacks 0566 "AtPrime source specialization"]
theorem maximalIdeal_iff_associatedPrime_atPrime :
    Ideal.IsWeaklyAssociatedToModule (Localization.AtPrime p)
        (LocalizedModule.AtPrime p M)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) ↔
      IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule.AtPrime p M) := sorry

end Ideal.IsWeaklyAssociatedToModule.Localization

end
