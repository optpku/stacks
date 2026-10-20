/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Tactic.CrossRefAttribute

/-!
# Nilpotence and Away Localizations

@stack 02C5
-/

@[expose] public section

universe u

namespace Localization.Away

variable {A : Type u} [CommSemiring A]

/-- Localization away from `f` is the zero ring exactly when `f` is nilpotent. -/
@[stacks 02C5 "away localization and nilpotence"]
theorem subsingleton_iff_isNilpotent (f : A) :
    Subsingleton (Localization.Away f) ↔ IsNilpotent f := by
  simpa [Localization.Away, isNilpotent_iff_zero_mem_powers] using
    (IsLocalization.subsingleton_iff :
      Subsingleton (Localization (Submonoid.powers f)) ↔ 0 ∈ Submonoid.powers f)

/-- Localization away from `f` is nontrivial exactly when `f` is not nilpotent. -/
@[stacks 02C5 "nontrivial away localization"]
theorem nontrivial_iff_not_isNilpotent (f : A) :
    Nontrivial (Localization.Away f) ↔ ¬ IsNilpotent f := by
  rw [← not_subsingleton_iff_nontrivial]
  exact not_congr (subsingleton_iff_isNilpotent f)

end Localization.Away
