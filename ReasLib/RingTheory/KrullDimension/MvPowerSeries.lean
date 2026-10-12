/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Regular
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

end MvPowerSeries
