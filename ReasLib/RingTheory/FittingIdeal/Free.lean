/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FittingIdeal.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fitting ideals of finite free modules

The intrinsic Fitting ideals of `Fin n -> R` are the zero ideal below rank `n` and the unit ideal
from rank `n` onward.

@stack 07ZB
-/

@[expose] public section

universe u

namespace FittingIdeal

variable (R : Type u) [CommRing R]

/-- The `k`th Fitting ideal of a free module of rank `n` is bottom below the rank and top from the
rank onward. -/
@[stacks 07ZB "Fitting ideals of finite free modules"]
theorem free_eq_bot_or_top (n k : ℕ) :
    fittingIdeal R (Fin n -> R) k = if k < n then ⊥ else ⊤ := sorry

/-- Below the rank, every Fitting ideal of a finite free module is the zero ideal. -/
@[stacks 07ZB "vanishing range for finite-free Fitting ideals"]
theorem free_eq_bot_of_lt {n k : ℕ} (hk : k < n) :
    fittingIdeal R (Fin n -> R) k = ⊥ := sorry

/-- At or above the rank, every Fitting ideal of a finite free module is the unit ideal. -/
@[stacks 07ZB "unit range for finite-free Fitting ideals"]
theorem free_eq_top_of_le {n k : ℕ} (hk : n ≤ k) :
    fittingIdeal R (Fin n -> R) k = ⊤ := sorry

end FittingIdeal
