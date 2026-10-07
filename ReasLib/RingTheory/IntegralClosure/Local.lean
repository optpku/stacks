module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local criteria for integrality

This leaf records the prime-local criterion for a single element to be
integral over the base ring.

@stack 034K
-/

@[expose] public section

universe u v

namespace IsIntegral

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- An element of an `R`-algebra is integral over `R` exactly when its image is
integral after localization at every prime of `R`.

This is Lemma 10.36.12 of the Stacks project. -/
@[stacks 034K]
theorem iff_forall_atPrime {x : S} :
    IsIntegral R x ↔
      ∀ p : PrimeSpectrum R,
        IsIntegral (Localization.AtPrime p.asIdeal)
          (algebraMap S
            (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) x) := sorry

end IsIntegral
