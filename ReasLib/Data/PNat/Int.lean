/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.PNat.Order

/-!
# Positive Natural Numbers from Integers

This module owns the canonical conversion of an integer known to be at least one into a positive
natural number.  It is deliberately independent of spectral sequences and other applications.
-/

@[expose] public section

namespace PNat

/-- Convert an integer `r ≥ 1` into the corresponding positive natural number. -/
@[stacks 0AMI "positive integral index"]
def ofInt (r : ℤ) (hr : 1 ≤ r) : ℕ+ :=
  ⟨Int.toNat r,
    Nat.pos_iff_ne_zero.mpr (fun h =>
      (not_le_of_gt Int.zero_lt_one) (hr.trans (Int.toNat_eq_zero.mp h)))⟩

/-- Coercing `ofInt r hr` back to `ℤ` recovers `r`. -/
theorem coe_ofInt (r : ℤ) (hr : 1 ≤ r) : (ofInt r hr : ℤ) = r := by
  have hr0 : (0 : ℤ) ≤ r := (zero_le_one : (0 : ℤ) ≤ 1).trans hr
  exact Int.toNat_of_nonneg hr0

/-- Converting the integer coercion of a positive natural number recovers that number. -/
theorem ofInt_coe (r : ℕ+) :
    ofInt (r : ℤ) (Int.ofNat_le.mpr (Nat.succ_le_iff.mpr r.pos)) = r := by
  apply PNat.eq
  simp [ofInt]

/-- Conversion from valid integer indices preserves the successor operation. -/
theorem ofInt_add_one (r : ℤ) (hr : 1 ≤ r) :
    ofInt (r + 1) (hr.trans (le_add_of_nonneg_right (Int.natCast_nonneg 1))) =
      ofInt r hr + 1 := by
  apply PNat.eq
  change (r + 1).toNat = r.toNat + 1
  apply Int.ofNat_injective
  change ((r + 1).toNat : ℤ) = ((r.toNat + 1 : ℕ) : ℤ)
  have hr0 : (0 : ℤ) ≤ r := (zero_le_one : (0 : ℤ) ≤ 1).trans hr
  have hr1 : (0 : ℤ) ≤ r + 1 := add_nonneg hr0 zero_le_one
  rw [Int.toNat_of_nonneg hr1, Int.natCast_add, Int.toNat_of_nonneg hr0]
  simp

end PNat
