/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Krull dimension of finite-variable formal power series

@stack 032C
-/

universe u

namespace MvPowerSeries

/-- Formal power series in `d` variables over a field have Krull dimension `d`. -/
@[stacks 032C "finite-variable formal power-series dimension"]
theorem ringKrullDim_fin_field (k : Type u) [Field k] (d : ℕ) :
    ringKrullDim (MvPowerSeries (Fin d) k) = d := sorry

/-- Formal power series in `d` variables over a DVR have Krull dimension `d + 1`.
This applies in particular to Cohen rings, without an equicharacteristic assumption. -/
@[stacks 032C "finite-variable formal power-series dimension over a DVR"]
theorem ringKrullDim_fin_dvr (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (d : ℕ) :
    ringKrullDim (MvPowerSeries (Fin d) R) = (d : WithBot ℕ∞) + 1 := sorry

end MvPowerSeries
