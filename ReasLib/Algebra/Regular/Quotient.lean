/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotients by regular elements

This leaf gives a canonical, specification-facing quotient for a divisibility
statement by a left-regular element.  The choice is internal to the owner;
downstream users reason through the multiplication and uniqueness API.
-/

@[expose] public section

noncomputable section

universe u

namespace IsLeftRegular

variable {R : Type u} [Monoid R]

/-- The unique right factor of `b` after division by a left-regular divisor `a`. -/
@[stacks 052Q "quotient by a left-regular divisor"]
noncomputable def quotient {a b : R} (ha : IsLeftRegular a)
    (hab : ∃ c, a * c = b) : R :=
  hab.choose

/-- Multiplying the regular divisor by its canonical quotient recovers the dividend. -/
@[stacks 052Q "left-regular quotient specification"]
theorem mul_quotient {a b : R} (ha : IsLeftRegular a) (hab : ∃ c, a * c = b) :
    a * ha.quotient hab = b := sorry

/-- A candidate is the canonical quotient exactly when multiplying it by the divisor recovers
the dividend. -/
@[stacks 052Q "left-regular quotient uniqueness"]
theorem quotient_eq_iff {a b c : R} (ha : IsLeftRegular a)
    (hab : ∃ d, a * d = b) :
    ha.quotient hab = c ↔ a * c = b := sorry

/-- The canonical quotient is independent of the proof of divisibility. -/
@[stacks 052Q "left-regular quotient proof independence"]
theorem quotient_congr {a b : R} (ha : IsLeftRegular a)
    (hab hab' : ∃ c, a * c = b) :
    ha.quotient hab = ha.quotient hab' := sorry

end IsLeftRegular
