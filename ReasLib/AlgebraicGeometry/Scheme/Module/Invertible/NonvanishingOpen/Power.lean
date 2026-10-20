/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NonvanishingOpen
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower

/-!
# Tensor powers on a nonvanishing open

An invertible-module section trivializes the module on its nonvanishing open. This file extends
that trivialization to nonnegative tensor powers and uses it to contract a corresponding twist.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}}

/-- On the nonvanishing open of a section of an invertible module, every nonnegative tensor
power is canonically trivial. -/
noncomputable def nonvanishingPowerTrivialization
    (L : X.Modules) [Invertible L] (s : Γ(L, ⊤)) (n : ℕ) :
    (L ^⊗ (n : ℤ)).over
        (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
          (RingedSpace.sectionFromTop L s)) ≅
      𝟙_ (SheafOfModules
        (X.ringCatSheaf.over
          (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
            (RingedSpace.sectionFromTop L s)))) :=
  let U := RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
    (RingedSpace.sectionFromTop L s)
  let R := SheafOfModules.RingedSite.Localization.restriction X.sheaf U
  let e : L.over U ≅ 𝟙_ (SheafOfModules (X.ringCatSheaf.over U)) :=
    (RingedSpace.SectionNonvanishing.trivialization X.toRingedSpace L
      (RingedSpace.sectionFromTop L s)).symm ≪≫
      R.mapIso (RingedSpace.unitIsoTensorUnit X.toRingedSpace) ≪≫
        (@Functor.Monoidal.εIso _ _ _ _ _ _ R
          (SheafOfModules.RingedSite.Localization.restrictionMonoidal X.sheaf U)).symm
  R.mapIso (RingedSpace.InvertiblePower.natIso L n).symm ≪≫
    R.mapIso (RingedSpace.TensorPower.monoidalComparison.iso L n).symm ≪≫
    (@Functor.Monoidal.tensorPowerIso
      (RingedSpace.Modules X.toRingedSpace)
      (SheafOfModules (X.ringCatSheaf.over U))
      SheafOfModules.instCategory SheafOfModules.instCategory
      (RingedSpace.modulesMonoidalCategory X.toRingedSpace) _ R
      (SheafOfModules.RingedSite.Localization.restrictionMonoidal X.sheaf U)
      L n).symm ≪≫
    tensorPowerMapIso e n ≪≫
      tensorPowerWithDegreeZeroSelfIso
        (Iso.refl (𝟙_ (SheafOfModules (X.ringCatSheaf.over U)))) n

/-- Restriction to the nonvanishing open followed by its power trivialization contracts a
nonnegative invertible-module twist. -/
noncomputable def nonvanishingTwistContraction
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (n : ℕ) :
    (F ⊗ (L ^⊗ (n : ℤ))).over
        (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
          (RingedSpace.sectionFromTop L s)) ⟶
      F.over (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
        (RingedSpace.sectionFromTop L s)) :=
  let U := RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
    (RingedSpace.sectionFromTop L s)
  let R := SheafOfModules.RingedSite.Localization.restriction X.sheaf U
  (@Functor.Monoidal.μIso _ _ _ _ _ _ R
      (SheafOfModules.RingedSite.Localization.restrictionMonoidal X.sheaf U)
      F (L ^⊗ (n : ℤ))).inv ≫
    (𝟙 (F.over U) ⊗ₘ (nonvanishingPowerTrivialization L s n).hom) ≫
      (ρ_ (F.over U)).hom

end AlgebraicGeometry.Scheme.Modules.Invertible
