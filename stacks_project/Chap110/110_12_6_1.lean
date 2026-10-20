/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.PowerSeries.NonflatLocalization
import StacksCheckRecall

@[expose] public section

universe u

variable (k : Type u) [Field k]

/- 110.12.6.1: for `R = k[y,z,a₁,a₂,…]/(y * aᵢ, aᵢ * aⱼ)` and `f` the
residue class of `z`, the displayed map `R⟦X⟧ ⟶ R_f⟦X⟧` localizes coefficients. -/
@[stacks 0ALD] #check
  (PowerSeries.NonflatLocalization.localizationMap k :
    PowerSeries (PowerSeries.NonflatLocalization.Ring k) →+*
      PowerSeries (Localization.Away (PowerSeries.NonflatLocalization.z k)))
