/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap10.Example_10_119_5.PowerSeriesModuleBridge

@[expose] public section

noncomputable section

universe u

open PowerSeries IsLocalRing
open AdicCompletion
open scoped Pointwise

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

open scoped PthPowerSubfield

/-- Helper for Chap10 Example 10 119 5: finite generic rank makes `k[[X]]` finite over the
coefficient DVR. -/
lemma moduleFinite_powerSeries_of_fractionRing_finiteDimensional_nonCircular
    (hfd : FiniteDimensional
      (FractionRing (finitePthPowerCoefficientSubring k p))
      (FractionRing (PowerSeries k))) :
    Module.Finite (finitePthPowerCoefficientSubring k p) (PowerSeries k) := sorry

end
