module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import ReasLib.RingTheory.Module.Support.BaseChange

/-!
# Support of a localized module

This leaf records the prime-by-prime support formula for localization.  It is
independent of Cohen--Macaulay or associated-prime arguments and is therefore
the shared owner for all such applications.
-/

@[expose] public section

universe u v

open PrimeSpectrum

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The support of `M` localized at `p` is detected by contracting primes of
`Rₚ` back to `R`. -/
theorem mem_support_localizationAtPrime_iff (p : PrimeSpectrum R)
    (q : PrimeSpectrum (Localization.AtPrime p.asIdeal)) :
    q ∈ support (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) ↔
      PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q ∈
        support R M := sorry

/-- Full support remains full after localization at a prime. -/
theorem support_localizationAtPrime_eq_univ_of_support_eq_univ
    (hsupp : support R M = Set.univ) (p : PrimeSpectrum R) :
    support (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) = Set.univ := sorry

end Module
