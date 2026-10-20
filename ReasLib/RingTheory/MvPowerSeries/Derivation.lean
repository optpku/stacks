/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

public section

universe u v

namespace MvPowerSeries

/-- The coefficient function of formal differentiation with respect to `X i`. -/
private noncomputable def partialDerivFun {k : Type u} [CommSemiring k] {σ : Type v}
    (i : σ) (f : MvPowerSeries σ k) : MvPowerSeries σ k :=
  fun n ↦ (n i + 1) • coeff (n + Finsupp.single i 1) f

/-- Formal differentiation preserves addition of power series. -/
private theorem partialDerivFun_add {k : Type u} [CommSemiring k] {σ : Type v}
    (i : σ) (f g : MvPowerSeries σ k) :
    partialDerivFun i (f + g) = partialDerivFun i f + partialDerivFun i g := sorry

/-- Formal differentiation commutes with scalar multiplication by coefficients. -/
private theorem partialDerivFun_smul {k : Type u} [CommSemiring k] {σ : Type v}
    (i : σ) (a : k) (f : MvPowerSeries σ k) :
    partialDerivFun i (a • f) = a • partialDerivFun i f := sorry

/-- The formal derivative of the constant power series `1` vanishes. -/
private theorem partialDerivFun_one {k : Type u} [CommSemiring k] {σ : Type v}
    (i : σ) : partialDerivFun i (1 : MvPowerSeries σ k) = 0 := sorry

/-- Formal differentiation satisfies the Leibniz identity for power series. -/
private theorem partialDerivFun_mul {k : Type u} [CommSemiring k] {σ : Type v}
    (i : σ) (f g : MvPowerSeries σ k) :
    partialDerivFun i (f * g) = f • partialDerivFun i g + g • partialDerivFun i f := sorry

/-- The formal partial derivative of a multivariate power series with respect to `X i`. -/
noncomputable def partialDeriv {k : Type u} [CommSemiring k] {σ : Type v}
    (i : σ) : Derivation k (MvPowerSeries σ k) (MvPowerSeries σ k) where
  toFun := partialDerivFun i
  map_add' := partialDerivFun_add i
  map_smul' := partialDerivFun_smul i
  map_one_eq_zero' := partialDerivFun_one i
  leibniz' := partialDerivFun_mul i

/-- The coefficient formula for the formal partial derivative. -/
theorem coeff_partialDeriv {k : Type u} [CommSemiring k] {σ : Type v}
    (i : σ) (f : MvPowerSeries σ k) (n : σ →₀ ℕ) :
    coeff n (partialDeriv i f) =
      (n i + 1) • coeff (n + Finsupp.single i 1) f := sorry

end MvPowerSeries
