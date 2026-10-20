module

public import Mathlib.RingTheory.Support
public import ReasLib.RingTheory.FittingIdeal.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07ZA
# Support detected by the zeroth Fitting ideal

The zeroth intrinsic Fitting ideal cuts out the support of a finite module.
This leaf keeps that support property independent of finite-presentation
results for higher Fitting ideals.
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The zero locus of the zeroth Fitting ideal of a finite module is its support. -/
@[stacks 07ZA "support cut out by the zeroth Fitting ideal"]
theorem zeroLocus_fittingIdeal_zero_eq_support [Module.Finite R M] :
    PrimeSpectrum.zeroLocus (fittingIdeal R M 0) = support R M := sorry

end Module
