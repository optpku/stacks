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
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
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

instance twoIdeal_isPrime : twoIdeal.IsPrime := sorry

/-- The local ring `Z_(2)`. -/
abbrev zLocalTwo := Localization.AtPrime twoIdeal

/-- The image of 2 in `Z_(2)`. -/
abbrev twoInZLocalTwo : zLocalTwo := algebraMap ℤ zLocalTwo (2 : ℤ)

/-- The localization `Z_(2)[1/2]`. -/
abbrev zLocalTwoAwayTwo := Localization.Away twoInZLocalTwo

/-- Localizing `Z_(2)` away from 2 gives its fraction field. -/
theorem zLocalTwoAwayTwo_isFractionRing : IsFractionRing zLocalTwo zLocalTwoAwayTwo := sorry

noncomputable instance zLocalTwoAwayTwo_field : Field zLocalTwoAwayTwo := by
  letI : IsFractionRing zLocalTwo zLocalTwoAwayTwo := zLocalTwoAwayTwo_isFractionRing
  exact IsFractionRing.toField zLocalTwo

/-- Example 10.35.15: `Z_(2)[1/2]` is canonically equivalent to `Q` as a `Z`-algebra. -/
@[stacks 00G7 "localization equivalence"]
noncomputable def zLocalTwoAwayTwoAlgEquivRat : zLocalTwoAwayTwo ≃ₐ[ℤ] ℚ := sorry

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
      (⊥ : PrimeSpectrum zLocalTwo) := sorry


#check @Localization.AtPrime
#check @Localization.Away
#check @IsFractionRing
