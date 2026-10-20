/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-- The second prime strictly larger than `768 * g`. -/
noncomputable def semistableReductionPrime (g : ℕ) : ℕ :=
  let ℓ' := sInf {p : ℕ | 768 * g < p ∧ p.Prime}
  sInf {p : ℕ | ℓ' < p ∧ p.Prime}

/-- The natural-number bound `(2 * g - 2) * Nat.factorial (ℓ ^ (2 * g))`,
where `ℓ` is the second prime strictly larger than `768 * g`. -/
noncomputable def semistableReductionBound (g : ℕ) : ℕ :=
  (2 * g - 2) * Nat.factorial (semistableReductionPrime g ^ (2 * g))

/-- The natural-number bound is given by its defining factorial formula for genus `g` at least `2`. -/
theorem semistableReductionBound_eq (g : ℕ) (h_genus : 2 ≤ g) :
    semistableReductionBound g =
      (2 * g - 2) * Nat.factorial (semistableReductionPrime g ^ (2 * g)) := sorry
