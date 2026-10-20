module

public import Mathlib.RingTheory.Localization.AsSubring

@[expose] public section

/-!
# Total Quotient Rings at a Prime

This module relates the total quotient ring of a commutative ring to a further
localization of a prime localization.
-/

universe u

namespace Localization.AtPrime

variable {R : Type u} [CommRing R]

/-- The total quotient ring of `R`, localized at the complement of a prime,
is a localization of the local ring at that prime by the images of the
nonzerodivisors of `R`. -/
theorem totalFraction_isLocalization (P : Ideal R) [P.IsPrime] :
    IsLocalization (Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors R))
      (Localization (Algebra.algebraMapSubmonoid (FractionRing R) P.primeCompl)) := sorry

end Localization.AtPrime
