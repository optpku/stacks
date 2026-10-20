/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.IdealPower
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.Limit.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presented Limits of Ideal-Power Derived Towers

This file specializes the generic presented-limit base-change construction to the canonical
quotients `A ⧸ I ^ (n + 1)`.  Its concrete object and map retain an explicit derived extension
model, while the generic owner remains visible underneath.
@stack 09AU
@stack 09AV
@stack 09AW
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.IdealPowerTower.Limit

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- Derived base change of an `A`-complex to the `n`th positive ideal-power quotient. -/
noncomputable abbrev baseChange
    (K : DerivedCategory (ModuleCat.{u, u} A)) (n : ℕ)
    (E : IdealPowerTower.Extension I n) :=
  DerivedTower.Limit.BaseChange.obj
    (CommRingCat.IdealPower.Positive.cone I) K n E

/-- The canonical map from the base change of a presented homotopy limit to stage `n`. -/
@[stacks 09AV "ideal-power limit base-change map",
  stacks 09AW "ideal-power limit base-change map",
  stacks 09AU "ideal-power limit base-change map"]
noncomputable def baseChangeMap (T : IdealPowerTower I)
    {K : DerivedCategory (ModuleCat.{u, u} A)}
    (P : HomotopyLimit.Presentation T.toBase K) (n : ℕ)
    (E : IdealPowerTower.Extension I n) :
    baseChange K n E ⟶ T.obj n :=
  DerivedTower.Limit.BaseChange.map
    T (CommRingCat.IdealPower.Positive.cone I) P n E

/-- The ideal-power base-change map transposes back to the stage projection of its presentation. -/
@[simp]
theorem baseChangeMap_untranspose (T : IdealPowerTower I)
    {K : DerivedCategory (ModuleCat.{u, u} A)}
    (P : HomotopyLimit.Presentation T.toBase K) (n : ℕ)
    (E : IdealPowerTower.Extension I n) :
    E.untranspose (baseChangeMap T P n E) = P.stageProjection n := sorry

end CategoryTheory.ModuleCat.IdealPowerTower.Limit
