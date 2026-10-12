/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Multiplicity
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Scalar

/-!
# Multiplicity of Two-Periodic Scalar Endomorphism Complexes

This file records finite-length and multiplicity results for two-periodic complexes whose
first differential is zero and whose second differential is scalar multiplication.
-/

@[expose] public section

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R]

/-- The homology of `ofZeroScalar M x` has finite length when `M` has support dimension at
most one and `M / xM` has support dimension at most zero. -/
theorem ofZeroScalar_homology_isFiniteLength
    [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hM : Module.supportDim R M ≤ 1)
    (hMx : Module.supportDim R (QuotSMulTop x M) ≤ 0) (i : ZMod 2) :
    IsFiniteLength R ((ofZeroScalar M x).toCochainComplex.homology i) := sorry

/-- If the support of a finite module consists of the closed point and finitely many distinct
nonclosed primes, the multiplicity of its zero-scalar complex is the sum of the scalar orders
at those primes weighted by the corresponding localized lengths. -/
theorem multiplicity_ofZeroScalar_eq_sum
    [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hM : Module.supportDim R M ≤ 1)
    (hMx : Module.supportDim R (QuotSMulTop x M) ≤ 0)
    {t : ℕ} (q : Fin t → PrimeSpectrum R) (hq : Function.Injective q)
    (hq_ne_closedPoint : ∀ i, q i ≠ IsLocalRing.closedPoint R)
    (hsupport : Module.support R M =
      Set.insert (IsLocalRing.closedPoint R) (Set.range q)) :
    (ofZeroScalar M x).multiplicity
        (ofZeroScalar_homology_isFiniteLength M x hM hMx 0)
        (ofZeroScalar_homology_isFiniteLength M x hM hMx 1) =
      ∑ i, ((Ring.ord (R ⧸ (q i).asIdeal)
          (Ideal.Quotient.mk (q i).asIdeal x)).toNat : ℤ) *
        ((Module.length (Localization.AtPrime (q i).asIdeal)
          (LocalizedModule.AtPrime (q i).asIdeal M)).toNat : ℤ) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
