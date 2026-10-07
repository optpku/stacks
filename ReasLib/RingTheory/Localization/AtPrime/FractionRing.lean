module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import ReasLib.RingTheory.Localization.FractionRing.Algebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fraction rings of prime localizations

This leaf records the canonical comparison between the fraction ring of a prime
localization and any chosen fraction-field model of the original domain.  The
prime-complement condition is discharged by the domain/prime instances; it is
kept in the construction rather than reproduced in chapter-facing proofs.
-/

@[expose] public section

universe u v w

namespace Localization.AtPrime

variable {A : Type u} {K : Type v}
variable [CommRing A] [IsDomain A]
variable [Field K] [Algebra A K] [IsFractionRing A K]

/-- Tag `00QF`: the fraction ring of a prime localization is canonically the
chosen fraction field of the original domain. -/
@[stacks 00QF "fraction ring of a prime localization"]
noncomputable def fractionRingAlgEquiv
    (p : Ideal A) [p.IsPrime] :
    letI : Algebra (Localization.AtPrime p) K :=
      IsLocalization.localizationAlgebraOfSubmonoidLe
        (Localization.AtPrime p) K p.primeCompl (nonZeroDivisors A)
        p.primeCompl_le_nonZeroDivisors
    letI : IsScalarTower A (Localization.AtPrime p) K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le
        (Localization.AtPrime p) K p.primeCompl (nonZeroDivisors A)
        p.primeCompl_le_nonZeroDivisors
    letI : IsFractionRing (Localization.AtPrime p) K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
        p.primeCompl (Localization.AtPrime p) K
    FractionRing (Localization.AtPrime p) ≃ₐ[Localization.AtPrime p] K :=
  letI : Algebra (Localization.AtPrime p) K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.AtPrime p) K p.primeCompl (nonZeroDivisors A)
      p.primeCompl_le_nonZeroDivisors
  letI : IsScalarTower A (Localization.AtPrime p) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.AtPrime p) K p.primeCompl (nonZeroDivisors A)
      p.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing (Localization.AtPrime p) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      p.primeCompl (Localization.AtPrime p) K
  FractionRing.algEquiv (A := Localization.AtPrime p) K

section RestrictScalars

/-- The specified `R`-scalar action on a fraction-field model is compatible with
the canonical action through a prime localization of `A`. -/
theorem isScalarTowerAtPrimeOver
    {R : Type u} {A : Type v} {K : Type w}
    [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra R K] [hTower : IsScalarTower R A K]
    (p : Ideal A) [p.IsPrime] :
    letI : Algebra (Localization.AtPrime p) K :=
      IsLocalization.localizationAlgebraOfSubmonoidLe
        (Localization.AtPrime p) K p.primeCompl (nonZeroDivisors A)
        p.primeCompl_le_nonZeroDivisors
    letI : SMul (Localization.AtPrime p) K :=
      (inferInstance : Algebra (Localization.AtPrime p) K).toSMul
    letI : IsScalarTower A (Localization.AtPrime p) K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le
        (Localization.AtPrime p) K p.primeCompl (nonZeroDivisors A)
        p.primeCompl_le_nonZeroDivisors
    letI : Algebra R (Localization.AtPrime p) := inferInstance
    IsScalarTower R (Localization.AtPrime p) K := sorry

variable {R : Type u} {A : Type v} {K : Type w}
variable [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Algebra R K] [hTower : IsScalarTower R A K]

/-- Tag `00QF`: restricting the canonical fraction-ring comparison of a prime
localization along a base algebra map.  It preserves the supplied `R`-algebra
structure on the fraction-field model while pinning Mathlib's standard
`R`-actions on the two localization-side fraction rings, so it composes with
ordinary `R`-algebra comparisons. -/
@[stacks 00QF "prime-localized fraction-ring comparison over a base"]
noncomputable def fractionRingAlgEquivOver
    (p : Ideal A) [p.IsPrime] :
    letI : Algebra (Localization.AtPrime p) K :=
      IsLocalization.localizationAlgebraOfSubmonoidLe
        (Localization.AtPrime p) K p.primeCompl (nonZeroDivisors A)
        p.primeCompl_le_nonZeroDivisors
    letI : SMul (Localization.AtPrime p) K :=
      (inferInstance : Algebra (Localization.AtPrime p) K).toSMul
    letI : IsScalarTower A (Localization.AtPrime p) K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le
        (Localization.AtPrime p) K p.primeCompl (nonZeroDivisors A)
        p.primeCompl_le_nonZeroDivisors
    letI : IsFractionRing (Localization.AtPrime p) K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
        p.primeCompl (Localization.AtPrime p) K
    letI : Algebra R (Localization.AtPrime p) := inferInstance
    letI : IsScalarTower R (Localization.AtPrime p) K :=
      isScalarTowerAtPrimeOver (R := R) (K := K) p
    letI : Algebra R (FractionRing (Localization.AtPrime p)) := inferInstance
    letI : IsScalarTower R (Localization.AtPrime p)
        (FractionRing (Localization.AtPrime p)) :=
      FractionRing.isScalarTower_algebraMap
        (R := R) (A := Localization.AtPrime p)
    FractionRing (Localization.AtPrime p) ≃ₐ[R] K :=
  letI : Algebra (Localization.AtPrime p) K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.AtPrime p) K p.primeCompl (nonZeroDivisors A)
      p.primeCompl_le_nonZeroDivisors
  letI : SMul (Localization.AtPrime p) K :=
    (inferInstance : Algebra (Localization.AtPrime p) K).toSMul
  letI : IsScalarTower A (Localization.AtPrime p) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.AtPrime p) K p.primeCompl (nonZeroDivisors A)
      p.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing (Localization.AtPrime p) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      p.primeCompl (Localization.AtPrime p) K
  letI : Algebra R (Localization.AtPrime p) := inferInstance
  letI : IsScalarTower R (Localization.AtPrime p) K :=
    isScalarTowerAtPrimeOver (R := R) (K := K) p
  letI : Algebra R (FractionRing (Localization.AtPrime p)) := inferInstance
  letI : IsScalarTower R (Localization.AtPrime p)
      (FractionRing (Localization.AtPrime p)) :=
    FractionRing.isScalarTower_algebraMap
      (R := R) (A := Localization.AtPrime p)
  (fractionRingAlgEquiv (A := A) (K := K) p).restrictScalars R

end RestrictScalars

end Localization.AtPrime
