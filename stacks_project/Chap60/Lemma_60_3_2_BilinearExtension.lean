/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
