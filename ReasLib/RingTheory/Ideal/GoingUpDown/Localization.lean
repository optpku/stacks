/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Inseparable
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

@[expose] public section

noncomputable section

open PrimeSpectrum Localization

universe u

namespace GoingUpDown.Localization

/-- The map from `ℤ` to the localization away from `11` is not specializing. -/
theorem not_specializingMap_comap_awayEleven :
    ¬ SpecializingMap (comap (algebraMap ℤ (Away (11 : ℤ)))) :=
  sorry

/-- Localization of `ℤ` away from `11` has the going-down property over `ℤ`. -/
instance hasGoingDown_awayEleven : Algebra.HasGoingDown ℤ (Away (11 : ℤ)) :=
  sorry

/-- The map from `ℤ` to the Gaussian-integer localization away from `2 + i` is specializing. -/
theorem specializingMap_comap_gaussianAway_twoPlusI :
    SpecializingMap (comap (algebraMap ℤ (Away (⟨2, 1⟩ : GaussianInt)))) :=
  sorry

/-- Localization of the Gaussian integers away from `2 + i` has the going-down property over `ℤ`. -/
instance hasGoingDown_gaussianAway_twoPlusI :
    Algebra.HasGoingDown ℤ (Away (⟨2, 1⟩ : GaussianInt)) :=
  sorry

/-- The map from `ℤ` to the Gaussian-integer localization away from `14 + 7i` is not specializing. -/
theorem not_specializingMap_comap_gaussianAway_fourteenPlusSevenI :
    ¬ SpecializingMap (comap (algebraMap ℤ (Away (⟨14, 7⟩ : GaussianInt)))) :=
  sorry

/-- Localization of the Gaussian integers away from `14 + 7i` has the going-down property over `ℤ`. -/
instance hasGoingDown_gaussianAway_fourteenPlusSevenI :
    Algebra.HasGoingDown ℤ (Away (⟨14, 7⟩ : GaussianInt)) :=
  sorry

end GoingUpDown.Localization
