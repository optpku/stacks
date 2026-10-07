module

public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Effective algebraic cycles

This file defines the additive submonoid of integer-valued algebraic cycles with nonnegative
coefficients.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/-- The additive submonoid of integer-valued algebraic cycles whose coefficients are
nonnegative. -/
def effective (X : Scheme.{u}) : AddSubmonoid (AlgebraicCycle X ℤ) :=
  AddSubmonoid.nonneg (AlgebraicCycle X ℤ)

/-- An algebraic cycle is effective exactly when each of its coefficients is nonnegative. -/
theorem mem_effective {X : Scheme.{u}} (α : AlgebraicCycle X ℤ) :
    α ∈ effective X ↔ ∀ x : X, 0 ≤ α x := sorry

end AlgebraicGeometry.AlgebraicCycle
