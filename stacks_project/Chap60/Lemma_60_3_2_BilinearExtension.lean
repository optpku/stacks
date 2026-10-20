/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.BilinearExtension

universe u

/- The predecessor divided power is zero at index zero. -/
#check
  (DividedPowers.BilinearExtension.dpowPred :
    ∀ {A : Type u} [CommRing A] {I : Ideal A}, DividedPowers I → ℕ → A → A)

/- The twice-predecessor divided power is zero at indices zero and one. -/
#check
  (DividedPowers.BilinearExtension.dpowPredTwo :
    ∀ {A : Type u} [CommRing A] {I : Ideal A}, DividedPowers I → ℕ → A → A)
