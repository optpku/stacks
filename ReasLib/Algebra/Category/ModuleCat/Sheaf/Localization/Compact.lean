/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.QuasiCompact
public import ReasLib.CategoryTheory.Preadditive.CompactObject
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compact localized structure modules

The localized structure module represented by a quasi-compact site object is compact.  This is
the categorical owner of the assertion that its represented additive Hom functor commutes with
arbitrary direct sums.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace SheafOfModules.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (R : Sheaf J RingCat.{w}) (U : C)
variable [(restriction R U : SheafOfModules.{w} R ⥤
  SheafOfModules.{w} (R.over U)).IsRightAdjoint]

/-- Lemma 18.30.4: the localized structure module represented by a quasi-compact object of a
ringed site is compact. -/
@[stacks 0936 "sieve-saturated specialization"]
theorem structureModule_isCompactObject (hU : J.QuasiCompactObject U) :
    IsCompactObject (structureModule R U) := sorry

end SheafOfModules.Localization

namespace SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C)
variable [(SheafOfModules.Localization.restriction
  (SheafOfModules.RingedSite.ringSheaf J 𝒪) U).IsRightAdjoint]

/-- Lemma 18.30.4 (0936), ringed-site notation: the object `j![𝒪, U]` represented by a
quasi-compact site object is compact. -/
@[stacks 0936 "sieve-saturated ringed-site notation"]
theorem isCompactObject (hU : J.QuasiCompactObject U) :
    IsCompactObject
      (SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero 𝒪 U) := sorry

end SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

namespace CategoryTheory.Coverage.QuasiCompactObject

variable {C : Type u} [Category.{v} C] {K : Coverage C} {U : C}
variable [HasWeakSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Lemma 18.30.4 (0936): the localized structure module represented by a quasi-compact object
of a chosen-cover ringed site is compact. -/
@[stacks 0936]
theorem structureModuleIsCompact
    (hU : K.QuasiCompactObject U) (R : Sheaf K.toGrothendieck RingCat.{w})
    [(SheafOfModules.Localization.restriction R U : SheafOfModules.{w} R ⥤
      SheafOfModules.{w} (R.over U)).IsRightAdjoint] :
    IsCompactObject (SheafOfModules.Localization.structureModule R U) := sorry

end CategoryTheory.Coverage.QuasiCompactObject
