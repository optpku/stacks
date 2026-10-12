/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth.SupportDim
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Regular
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Support
public import ReasLib.RingTheory.Module.Support.PrimeSpan

@[expose] public section

universe u v

namespace IsSMulRegular

/-- A scalar regular on a finite module remains regular on the quotient by a minimal point of
the module's support. -/
theorem quotient_of_minimalSupport
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {r : R} (hr : IsSMulRegular M r) (p : PrimeSpectrum R)
    (hp : Minimal (· ∈ Module.support R M) p) :
    IsSMulRegular (R ⧸ p.asIdeal) r := sorry

end IsSMulRegular

namespace Module

/-- The quotient by a minimal point of a one-dimensional module support again has support
dimension one over the original local ring. -/
theorem supportDim_quotient_eq_one_of_minimalSupport
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hdim : supportDim R M = 1) (p : PrimeSpectrum R)
    (hp : Minimal (· ∈ support R M) p) :
    supportDim R (R ⧸ p.asIdeal) = 1 := sorry

/-- Localizing a finite module at a minimal point of its support gives a finite-length module. -/
theorem isFiniteLength_localizedAtPrime_of_minimalSupport
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : PrimeSpectrum R) (hp : Minimal (· ∈ support R M) p) :
    IsFiniteLength (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) := sorry

end Module
