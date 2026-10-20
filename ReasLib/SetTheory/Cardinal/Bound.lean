/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

noncomputable section

universe u

open scoped Cardinal

namespace Cardinal

/-- The maximum of the countable power of a cardinal and its successor cardinal. -/
noncomputable def countableSuccBound (kappa : Cardinal.{u}) : Cardinal.{u} :=
  max (kappa ^ ℵ₀) (Order.succ kappa)

/-- The countable-successor bound is the maximum of the countable power and the successor. -/
theorem countableSuccBound_eq (kappa : Cardinal.{u}) :
    countableSuccBound kappa = max (kappa ^ ℵ₀) (Order.succ kappa) := sorry

/-- The countable power of a cardinal is at most its countable-successor bound. -/
theorem power_le_countableSuccBound (kappa : Cardinal.{u}) :
    kappa ^ ℵ₀ ≤ countableSuccBound kappa := sorry

/-- The successor of a cardinal is at most its countable-successor bound. -/
theorem succ_le_countableSuccBound (kappa : Cardinal.{u}) :
    Order.succ kappa ≤ countableSuccBound kappa := sorry

end Cardinal
