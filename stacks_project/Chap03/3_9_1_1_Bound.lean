module

public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

noncomputable section

universe u

open scoped Cardinal

namespace AlgebraicGeometry.Scheme

/-- The Stacks cardinal function sending `κ` to `max (κ ^ ℵ₀) (Order.succ κ)`. -/
noncomputable def bound (κ : Cardinal.{u}) : Cardinal.{u} :=
  max (κ ^ ℵ₀) (Order.succ κ)

/-- Cardinal exponential `κ ^ ℵ₀` is at most `bound κ`. -/
theorem power_le_bound (κ : Cardinal.{u}) : κ ^ ℵ₀ ≤ bound κ := sorry

/-- The successor cardinal `Order.succ κ` is at most `bound κ`. -/
theorem succ_le_bound (κ : Cardinal.{u}) : Order.succ κ ≤ bound κ := sorry

end AlgebraicGeometry.Scheme
