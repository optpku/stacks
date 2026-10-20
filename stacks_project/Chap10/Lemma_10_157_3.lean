/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.SerreCondition.Reduced
import StacksCheckRecall

@[expose] public section

/-! @stack 031R -/

/-!
# Reducedness and Serre Conditions

The low-degree Serre criterion is owned by `ReasLib`; this chapter file keeps the source-facing
statement and exposes the reusable directional API.
-/

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Lemma 10.157.3, tag `031R`: a Noetherian ring is reduced exactly when it satisfies `(R₀)` and
`(S₁)`. -/
@[stacks 031R]
#check (IsReduced.iff_serre (R := R) :
  IsReduced R ↔ R ⊧ (R₀) ∧ R ⊧ (S₁))

#check @IsReduced.serreConditionR_zero
#check @IsReduced.serreConditionS_one
#check @IsReduced.of_serre
