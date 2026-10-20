/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Weil

/-!
# Effective Weil divisors

Coefficientwise effectivity and elementary constructions for Weil divisors.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.WeilDivisor

/-- A Weil divisor is effective when every prime coefficient is nonnegative. -/
def IsEffective {X : Scheme.{u}} (D : Div(X)) : Prop :=
  ∀ Z : PrimeDivisor X, 0 ≤ D.coeff Z

/-- Effectivity of a Weil divisor is nonnegativity of all prime coefficients. -/
theorem isEffective_iff {X : Scheme.{u}} (D : Div(X)) :
    IsEffective D ↔ ∀ Z : PrimeDivisor X, 0 ≤ D.coeff Z := Iff.rfl

/-- The zero Weil divisor is effective. -/
theorem isEffective_zero (X : Scheme.{u}) : IsEffective (0 : Div(X)) := by
  intro Z
  simp

/-- The sum of effective Weil divisors is effective. -/
theorem isEffective_add {X : Scheme.{u}} {D E : Div(X)}
    (hD : IsEffective D) (hE : IsEffective E) : IsEffective (D + E) := by
  intro Z
  simpa using add_nonneg (hD Z) (hE Z)

/-- A prime Weil divisor is effective. -/
theorem isEffective_single {X : Scheme.{u}} (Z : PrimeDivisor X) :
    IsEffective (WeilDivisor.single Z) := by
  intro W
  classical
  simp only [WeilDivisor.coeff_single]
  split_ifs <;> norm_num

end AlgebraicGeometry.WeilDivisor
