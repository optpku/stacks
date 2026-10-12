/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap10.Example_10_119_5.CoefficientDVRCompletion
import StacksCheckRecall

/-!
# Fraction field of the finite-power coefficient ring

@stack 00PB
-/

@[expose] public section

noncomputable section

universe u

open PowerSeries IsLocalRing
open AdicCompletion
open scoped Pointwise

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

open scoped PthPowerSubfield

local notation "A" => finitePthPowerCoefficientSubring k p

/-- Helper for Example 10.119.5: the fraction-field extension
`Frac(A) ⊆ Frac(k[[X]])` is purely inseparable. -/
@[stacks 00PB "purely inseparable fraction-field extension"]
theorem finitePthPowerCoefficientSubring_fractionRing_isPurelyInseparable :
    IsPurelyInseparable (FractionRing ↥A) (FractionRing (PowerSeries k)) := sorry

@[stacks 00PB "purely inseparable fraction-field extension"]
#check @finitePthPowerCoefficientSubring_fractionRing_isPurelyInseparable
