/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat base change for ideal-power annihilated module sheaves

This leaf owns the same-site base-change criterion: a flat structure-sheaf map which is an
isomorphism after quotienting by an ideal induces an isomorphism on every module sheaf uniformly
annihilated by a power of that ideal.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite.IdealPower.IsAnnihilated

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O O' : Sheaf J CommRingCat.{u}}

/-- Lemma 18.28.16 (0GLY): flat base change is an isomorphism on module sheaves uniformly
annihilated by a power of an ideal whenever the induced quotient-sheaf map is an isomorphism. -/
@[stacks 0GLY]
theorem baseChangeUnit_isIso
    (alpha : O ⟶ O') (hflat : IsFlatHom alpha)
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory J O)
    [IsIso (IdealSheaf.TargetQuotient.ringMap alpha I)]
    (hF : IdealPower.IsAnnihilated I F) :
    IsIso
      ((SheafOfModules.pullbackPushforwardAdjunction
        (ringedSiteStructureMap alpha)).unit.app F) := sorry

end SheafOfModules.RingedSite.IdealPower.IsAnnihilated
