/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.ZMod
public import ReasLib.RingTheory.Completion.CohenRing
public import ReasLib.RingTheory.Smooth.Adic.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic Formal Smoothness of Power Series Rings

The canonical coefficient maps into a finite-variable formal power series ring are formally
smooth for its maximal-ideal-adic topology in equal characteristic and over a Cohen ring.

@stack 07NL
-/

@[expose] public section

open IsLocalRing

universe u v

section CharacteristicZero

variable {σ : Type v} [Finite σ] (K : Type u) [Field K] [CharZero K]

/-- Lemma 15.39.1 (1) (Stacks `07NL`): for a characteristic-zero field `K`, the canonical map
`ℚ → MvPowerSeries σ K` is formally smooth for the maximal-ideal-adic topology when `σ` is
finite. -/
@[stacks 07NL "characteristic-zero power series"]
theorem rational_to_mvPowerSeries_formally_smooth_for_madic :
    (algebraMap ℚ (MvPowerSeries σ K)).formally_smooth_for_adic
      (maximalIdeal (MvPowerSeries σ K)) := sorry

end CharacteristicZero

section PositiveCharacteristic

variable {σ : Type v} [Finite σ] (L : Type u) [Field L]
variable {p : ℕ} [Fact p.Prime] [CharP L p]

/-- Local instance justification (instance diamond): use the canonical prime-field algebra only
while stating the coefficient map into the power series ring. -/
local instance : Algebra (ZMod p) L := ZMod.algebra L p

/-- Lemma 15.39.1 (2) (Stacks `07NL`): for a field `L` of characteristic `p`, the canonical map
`ZMod p → MvPowerSeries σ L` is formally smooth for the maximal-ideal-adic topology when `σ` is
finite. -/
@[stacks 07NL "positive-characteristic power series"]
theorem zmod_to_mvPowerSeries_formally_smooth_for_madic :
    (algebraMap (ZMod p) (MvPowerSeries σ L)).formally_smooth_for_adic
      (maximalIdeal (MvPowerSeries σ L)) := sorry

end PositiveCharacteristic

section CohenRing

variable {σ : Type v} [Finite σ] (Λ : Type u) [CommRing Λ] [IsCohenRing Λ]

/-- Lemma 15.39.1 (3) (Stacks `07NL`): for a Cohen ring `Λ`, the canonical map
`ℤ → MvPowerSeries σ Λ` is formally smooth for the maximal-ideal-adic topology when `σ` is
finite. -/
@[stacks 07NL "Cohen-ring power series"]
theorem int_to_mvPowerSeries_over_cohenRing_formally_smooth_for_madic :
    (algebraMap ℤ (MvPowerSeries σ Λ)).formally_smooth_for_adic
      (maximalIdeal (MvPowerSeries σ Λ)) := sorry

end CohenRing
