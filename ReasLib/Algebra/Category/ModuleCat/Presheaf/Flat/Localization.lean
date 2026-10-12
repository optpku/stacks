/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat structure modules for slice localizations

The canonical object is `Localization.structureModule`: the unit module on a slice, extended by
lower shriek.  A reusable scoped `j![𝒪, U]` notation is supplied for the sheaf version.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v

namespace PresheafOfModules.Localization

variable {C : Type u} [Category.{u} C]

/-- The unit module on `C / U`, extended by lower shriek to `C`. -/
@[stacks 03EV "presheaf localized structure module"]
noncomputable abbrev structureModule
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    PresheafOfModules (ringPresheaf 𝒪) :=
  (PresheafOfModules.pullback
      (𝟙 ((Over.forget U).op ⋙ ringPresheaf 𝒪))).obj
    (PresheafOfModules.unit ((Over.forget U).op ⋙ ringPresheaf 𝒪))

/-- A localized structure module represented by an object is flat. -/
@[stacks 03EV "presheaf", instance]
theorem structureModule_isFlat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    PresheafOfModules.IsFlat (structureModule 𝒪 U) := sorry

end PresheafOfModules.Localization

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]

/-- The structure module on the slice over `U`, extended by sheaf lower shriek. -/
@[stacks 05NH "localized structure module", stacks 05NI "generator"]
noncomputable abbrev localizedStructureModuleExtensionByZero
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C)
    [(SheafOfModules.Localization.restriction (ringSheaf J 𝒪) U).IsRightAdjoint] :
    ringedSiteModuleCategory J 𝒪 :=
  SheafOfModules.Localization.structureModule (ringSheaf J 𝒪) U

namespace LocalizedStructureModuleExtensionByZero

/-- Standard notation for the structure module on `C / U`, extended by lower shriek. -/
scoped notation:max "j![" 𝒪:max ", " U:max "]" =>
  localizedStructureModuleExtensionByZero 𝒪 U

end LocalizedStructureModuleExtensionByZero

/-- Flatness is preserved by restriction to a slice site. -/
@[stacks 0E8J, instance]
theorem isFlat_over
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C)
    [HasWeakSheafify (J.over U) AddCommGrpCat]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat]
    (ℱ : ringedSiteModuleCategory J 𝒪)
    [IsFlat 𝒪 ℱ] :
    IsFlat (𝒪.over U) (ℱ.over U) := sorry

/-- The structure module represented by an object of a ringed site is flat. -/
@[stacks 03EV "sheaf", stacks 05NH, instance]
theorem localizedStructureModuleExtensionByZero_isFlat
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C)
    [(SheafOfModules.Localization.restriction (ringSheaf J 𝒪) U).IsRightAdjoint] :
    IsFlat 𝒪 (localizedStructureModuleExtensionByZero 𝒪 U) := sorry

end SheafOfModules.RingedSite
