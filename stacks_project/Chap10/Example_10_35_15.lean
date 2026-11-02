/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import StacksCheckRecall

/-!
# Localizing `Z_(2)` away from 2

@stack 00G7

Example 10.35.15 shows why the Jacobson hypothesis cannot be omitted from Lemma 10.35.14. The
concrete localization rings and their equivalence with `Q` are retained; the intermediate
classification of the basic open is proof infrastructure.
-/

@[expose] public section

open PrimeSpectrum IsLocalRing IsFractionRing

/-- The prime ideal `(2)` of `Z`. -/
abbrev twoIdeal : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)

instance twoIdeal_isPrime : twoIdeal.IsPrime :=
  (Ideal.span_singleton_prime (two_ne_zero : (2 : ℤ) ≠ 0)).mpr Int.prime_two

/-- The local ring `Z_(2)`. -/
abbrev zLocalTwo := Localization.AtPrime twoIdeal

/-- The image of 2 in `Z_(2)`. -/
abbrev twoInZLocalTwo : zLocalTwo := algebraMap ℤ zLocalTwo (2 : ℤ)

/-- The localization `Z_(2)[1/2]`. -/
abbrev zLocalTwoAwayTwo := Localization.Away twoInZLocalTwo

/-- Localizing `Z_(2)` away from 2 gives its fraction field. -/
theorem zLocalTwoAwayTwo_isFractionRing : IsFractionRing zLocalTwo zLocalTwoAwayTwo := by
  have htwo : twoInZLocalTwo ≠ 0 :=
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors zLocalTwo
      twoIdeal.primeCompl_le_nonZeroDivisors (by simp)
  refine IsLocalization.of_le (Submonoid.powers twoInZLocalTwo) (nonZeroDivisors zLocalTwo)
    (powers_le_nonZeroDivisors_of_noZeroDivisors htwo) ?_
  intro r hr
  have hr0 : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq twoIdeal.primeCompl r
  have ha : a ≠ 0 := by
    rintro rfl
    exact hr0 (IsLocalization.mk'_zero s)
  obtain ⟨n, b, hb, hab⟩ := WfDvdMonoid.max_power_factor ha Int.prime_two.irreducible
  have hbunit : IsUnit (algebraMap zLocalTwo zLocalTwoAwayTwo (algebraMap ℤ zLocalTwo b)) :=
    (IsLocalization.map_units zLocalTwo
      (⟨b, by simpa only [twoIdeal, Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton] using hb⟩ :
        twoIdeal.primeCompl)).map
        (algebraMap zLocalTwo zLocalTwoAwayTwo)
  have hmul : IsUnit
      (algebraMap zLocalTwo zLocalTwoAwayTwo (IsLocalization.mk' zLocalTwo a s) *
        algebraMap zLocalTwo zLocalTwoAwayTwo (algebraMap ℤ zLocalTwo s)) := by
    rw [← map_mul, IsLocalization.mk'_spec, hab, map_mul, map_pow, map_mul, map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit twoInZLocalTwo).pow n).mul hbunit
  exact isUnit_of_mul_isUnit_left hmul

noncomputable instance zLocalTwoAwayTwo_field : Field zLocalTwoAwayTwo := by
  letI : IsFractionRing zLocalTwo zLocalTwoAwayTwo := zLocalTwoAwayTwo_isFractionRing
  exact IsFractionRing.toField zLocalTwo

/-- Example 10.35.15: `Z_(2)[1/2]` is canonically equivalent to `Q` as a `Z`-algebra. -/
@[stacks 00G7 "localization equivalence"]
noncomputable def zLocalTwoAwayTwoAlgEquivRat : zLocalTwoAwayTwo ≃ₐ[ℤ] ℚ := by
  letI : IsFractionRing zLocalTwo zLocalTwoAwayTwo := zLocalTwoAwayTwo_isFractionRing
  have h : (nonZeroDivisors zLocalTwo).comap (algebraMap ℤ zLocalTwo) = nonZeroDivisors ℤ := by
    ext n
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact not_congr (IsLocalization.to_map_eq_zero_iff zLocalTwo
      twoIdeal.primeCompl_le_nonZeroDivisors)
  letI : IsFractionRing ℤ zLocalTwoAwayTwo := by
    rw [IsFractionRing, ← h]
    exact IsLocalization.localization_localization_isLocalization_of_has_all_units
      twoIdeal.primeCompl (nonZeroDivisors zLocalTwo) zLocalTwoAwayTwo
      (fun _ hx => hx.mem_nonZeroDivisors)
  exact IsLocalization.algEquiv (nonZeroDivisors ℤ) zLocalTwoAwayTwo ℚ

/-- The localization equivalence respects the structure map from `Z`. -/
@[simp]
theorem zLocalTwoAwayTwoAlgEquivRat_commutes (n : ℤ) :
    zLocalTwoAwayTwoAlgEquivRat (algebraMap ℤ zLocalTwoAwayTwo n) = algebraMap ℤ ℚ n :=
  AlgEquiv.commutes zLocalTwoAwayTwoAlgEquivRat n

/-- Example 10.35.15: the unique closed point of `Spec(Z_(2)[1/2])` contracts to the generic
point of `Spec(Z_(2))`. -/
@[stacks 00G7 "closed point maps to the generic point"]
theorem zLocalTwo_comap_closedPoint_eq_genericPoint :
    comap (algebraMap zLocalTwo zLocalTwoAwayTwo) (closedPoint zLocalTwoAwayTwo) =
      (⊥ : PrimeSpectrum zLocalTwo) := by
  letI : IsFractionRing zLocalTwo zLocalTwoAwayTwo := zLocalTwoAwayTwo_isFractionRing
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap zLocalTwo zLocalTwoAwayTwo)
    (closedPoint zLocalTwoAwayTwo).asIdeal = ⊥
  rw [Ideal.eq_bot_of_prime (closedPoint zLocalTwoAwayTwo).asIdeal]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective zLocalTwo zLocalTwoAwayTwo)


#check @Localization.AtPrime
#check @Localization.Away
#check @IsFractionRing
