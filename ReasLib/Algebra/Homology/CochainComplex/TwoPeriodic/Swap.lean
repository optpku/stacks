/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Swapping the Differentials of a Two-Periodic Endomorphism

This file defines the two-periodic endomorphism obtained by exchanging its two differentials
and records that this operation preserves acyclicity.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The two-periodic endomorphism obtained by exchanging its two differentials. -/
def swap (K : TwoPeriodicEndomorphism C) : TwoPeriodicEndomorphism C where
  X := K.X
  d₀ := K.d₁
  d₁ := K.d₀
  d₀_d₁ := K.d₁_d₀
  d₁_d₀ := K.d₀_d₁

/-- Exchanging the differentials preserves acyclicity of the associated two-periodic
complex. -/
theorem swap_acyclic_iff (K : TwoPeriodicEndomorphism C) :
    (swap K).toCochainComplex.Acyclic ↔ K.toCochainComplex.Acyclic := sorry

end CategoryTheory.TwoPeriodicEndomorphism
