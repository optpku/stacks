/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Dimension at most one from Krull dimension

This leaf owns the elementary dimension-one implication for domains.  It is
independent of locality, integral closures, and valuation-theoretic applications.
-/

@[expose] public section

universe u

namespace Ring

/-- A domain of ring Krull dimension one has dimension at most one. -/
@[stacks 09IG "dimension at most one from Krull dimension one"]
theorem dimensionLEOne_of_ringKrullDim_eq_one
    {R : Type u} [CommRing R] [IsDomain R]
    (hdim : ringKrullDim R = 1) :
    Ring.DimensionLEOne R := by
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  exact ⟨fun hne hp ↦ hp.isMaximal_of_ne_bot hne⟩

/-- A nontrivial ring of dimension at most one has finite Krull dimension. -/
instance finiteRingKrullDim_of_dimensionLEOne
    {R : Type u} [CommRing R] [Nontrivial R] [Ring.DimensionLEOne R] :
    FiniteRingKrullDim R := by
  apply finiteRingKrullDim_iff_ne_bot_and_top.mpr
  constructor
  · exact ne_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞))
      ringKrullDim_nonneg_of_nontrivial)
  · exact ne_of_lt ((Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 R)).trans_lt
      (WithBot.coe_lt_coe.mpr (ENat.coe_lt_top 1)))

end Ring
