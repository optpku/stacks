/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.Normal.Local
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Normal Rings and Serre's Criterion

This leaf owns the Noetherian Serre criterion for normality.  The normal-ring owner and the
parameterized Serre conditions remain separate, so downstream code can use either the canonical
instances or the source-facing equivalence.
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R]

namespace IsNormalRing

/-- A Noetherian normal ring satisfies Serre's condition `(R₁)`. -/
@[stacks 031S "normal rings satisfy R₁"]
instance serreConditionR_one [IsNoetherianRing R] [IsNormalRing R] : R ⊧ (R₁) := sorry

/-- A Noetherian normal ring satisfies Serre's condition `(S₂)`. -/
@[stacks 031S "normal rings satisfy S₂"]
instance serreConditionS_two [IsNoetherianRing R] [IsNormalRing R] : R ⊧ (S₂) := sorry

/-- Serre's conditions `(R₁)` and `(S₂)` imply normality. -/
@[stacks 031S "normality from R₁ and S₂"]
theorem of_serre (hR : R ⊧ (R₁)) (hS : R ⊧ (S₂)) : IsNormalRing R := sorry

/-- A Noetherian commutative ring is normal exactly when it satisfies `(R₁)` and `(S₂)`. -/
@[stacks 031S "normality and Serre conditions"]
theorem iff_serre [IsNoetherianRing R] :
    IsNormalRing R ↔ R ⊧ (R₁) ∧ R ⊧ (S₂) := sorry

end IsNormalRing
