/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPowerSeries.PhamBrieskorn
import StacksCheckRecall

/- Example 89.9.2 -/
@[stacks 0AEA] #check
  (MvPowerSeries.PhamBrieskorn.not_uniqueFactorizationMonoid :
    ∀ {r s t : ℕ}, 1 < r → r < s → s < t → Nat.Coprime r s → Nat.Coprime r t →
      Nat.Coprime s t → ¬ (r = 2 ∧ s = 3 ∧ t = 5) →
        ¬ UniqueFactorizationMonoid (MvPowerSeries.PhamBrieskorn.Ring r s t))

#check
  (MvPowerSeries.PhamBrieskorn.psi :
    rootsOfUnity 7 ℂ →
      MvPowerSeries.PhamBrieskorn.Ring 2 5 7 →+* PowerSeries ℂ)

#check
  (MvPowerSeries.PhamBrieskorn.not_uniqueFactorizationMonoid_two_five_seven :
    ¬ UniqueFactorizationMonoid (MvPowerSeries.PhamBrieskorn.Ring 2 5 7))
