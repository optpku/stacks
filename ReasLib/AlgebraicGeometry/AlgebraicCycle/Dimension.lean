/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Algebraic cycles of fixed dimension

This file defines the additive subgroup of algebraic cycles supported at points of a prescribed
value of an integer-valued dimension function.
-/

public section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Scheme.{u}}

/-- The zero cycle is supported in every prescribed dimension. -/
private theorem zero_mem_dimensionSubgroup_carrier (d : X → ℤ) (k : ℤ) :
    ∀ x, (0 : AlgebraicCycle X ℤ) x ≠ 0 → d x = k := sorry

/-- The sum of two cycles supported in dimension `k` is supported in dimension `k`. -/
private theorem add_mem_dimensionSubgroup_carrier (d : X → ℤ) (k : ℤ)
    {α β : AlgebraicCycle X ℤ}
    (hα : ∀ x, α x ≠ 0 → d x = k) (hβ : ∀ x, β x ≠ 0 → d x = k) :
    ∀ x, (α + β) x ≠ 0 → d x = k := sorry

/-- The negative of a cycle supported in dimension `k` is supported in dimension `k`. -/
private theorem neg_mem_dimensionSubgroup_carrier (d : X → ℤ) (k : ℤ)
    {α : AlgebraicCycle X ℤ} (hα : ∀ x, α x ≠ 0 → d x = k) :
    ∀ x, (-α) x ≠ 0 → d x = k := sorry

/-- The additive subgroup of algebraic cycles whose nonzero coefficients occur only at points
of dimension `k` according to `d`. -/
def dimensionSubgroup (d : X → ℤ) (k : ℤ) : AddSubgroup (AlgebraicCycle X ℤ) where
  carrier := {α | ∀ x, α x ≠ 0 → d x = k}
  zero_mem' := zero_mem_dimensionSubgroup_carrier d k
  add_mem' := add_mem_dimensionSubgroup_carrier d k
  neg_mem' := neg_mem_dimensionSubgroup_carrier d k

/-- Membership in `dimensionSubgroup d k` means that every point with a nonzero coefficient has
dimension `k`. -/
theorem mem_dimensionSubgroup (d : X → ℤ) (k : ℤ) (α : AlgebraicCycle X ℤ) :
    α ∈ dimensionSubgroup d k ↔ ∀ x, α x ≠ 0 → d x = k := sorry

end AlgebraicGeometry.AlgebraicCycle
