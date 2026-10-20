module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.35.16
@stack 00G8
-/

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum IsLocalRing

@[stacks 00G8 "injective contraction of the zero ideal"]
#check @Ideal.comap_bot_of_injective

@[stacks 00G8 "fraction-ring injectivity"]
#check @IsFractionRing.injective

-- Example 10.35.16: source-shaped specialization to the fraction field `ℚ / ℤ`.
@[stacks 00G8]
#check
  (show comap (algebraMap ℤ ℚ) (closedPoint ℚ) = (⊥ : PrimeSpectrum ℤ) from by
    rw [show closedPoint ℚ = (⊥ : PrimeSpectrum ℚ) by
      exact Subsingleton.elim _ _]
    simpa [PrimeSpectrum.ext_iff] using
      (Ideal.comap_bot_of_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ) :
        Ideal.comap (algebraMap ℤ ℚ) ⊥ = (⊥ : Ideal ℤ)))
