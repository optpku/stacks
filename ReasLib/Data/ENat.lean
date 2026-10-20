module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Elementary extended-natural order bridges

These small lemmas package the exact successor and predecessor shapes that
arise in depth and dimension estimates.  They are thin companions to
Mathlib's general `ENat.le_sub_of_add_le_right` API.
-/

@[expose] public section

namespace ENat

/-- A successor lower bound on an extended natural yields the predecessor lower bound. -/
@[stacks 00N0 "extended-natural predecessor bound", stacks 00NG "extended-natural predecessor bound"]
theorem coe_le_sub_one_of_succ_le {a : ℕ} {b : ℕ∞}
    (h : ((a + 1 : ℕ) : ℕ∞) ≤ b) :
    (a : ℕ∞) ≤ b - 1 := by
  exact ENat.le_sub_of_add_le_right ENat.one_ne_top (by simpa using h)

/-- Adding one to an extended natural is always at least one. -/
@[stacks 00N0 "extended-natural unit lower bound"]
theorem one_le_add_one (a : ℕ∞) : (1 : ℕ∞) ≤ a + 1 := by
  exact self_le_add_left 1 a

end ENat
