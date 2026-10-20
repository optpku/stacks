/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying sheaves of localization lower shriek

Forgetting module structure commutes with restriction to a slice site.  Taking the mate of this
strict right-adjoint square gives the canonical comparison between additive lower shriek and the
underlying additive sheaf of module lower shriek.  Its invertibility is kept as a property of an
explicit natural transformation, rather than as deferred inverse data.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The unit module on a localized site, viewed as its underlying additive sheaf. -/
@[stacks 0799 "localized structure sheaf"]
abbrev unitUnderlying (R : Sheaf J RingCat.{w}) (U : C) :
    Sheaf (J.over U) AddCommGrpCat.{w} :=
  (SheafOfModules.toSheaf (R.over U)).obj (SheafOfModules.unit (R.over U))

variable (R : Sheaf J RingCat.{w}) (U : C)
variable [(restriction R U : SheafOfModules.{z} R ⥤
  SheafOfModules.{z} (R.over U)).IsRightAdjoint]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [∀ P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{z},
  (Over.forget U).op.HasLeftKanExtension P]

/-- Forgetting module structure strictly commutes with restriction to the slice site. -/
@[stacks 08P4 "underlying restriction comparison"]
noncomputable def underlyingRestrictionIso :
    (restriction R U : SheafOfModules.{z} R ⥤
        SheafOfModules.{z} (R.over U)) ⋙
        SheafOfModules.toSheaf (R.over U) ≅
      SheafOfModules.toSheaf R ⋙
        (Over.forget U).sheafPushforwardContinuous
          AddCommGrpCat.{z} (J.over U) J :=
  Iso.refl _

/-- The mate comparison from additive localization lower shriek to the underlying additive sheaf
of module localization lower shriek. -/
@[stacks 08P4 "underlying lower-shriek comparison"]
noncomputable def underlyingLowerShriekComparison :
    SheafOfModules.toSheaf (R.over U) ⋙
        (Over.forget U).sheafPullback AddCommGrpCat.{z} (J.over U) J ⟶
      (lowerShriek R U : SheafOfModules.{z} (R.over U) ⥤
        SheafOfModules.{z} R) ⋙ SheafOfModules.toSheaf R :=
  ((mateEquiv
      (lowerShriekRestrictionAdj R U)
      ((Over.forget U).sheafAdjunctionContinuous
        AddCommGrpCat.{z} (J.over U) J)).symm
    (underlyingRestrictionIso R U).hom).natTrans

/-- The mate comparison between additive and module localization lower shriek is invertible. -/
@[stacks 08P4]
theorem underlyingLowerShriekComparison_isIso :
    IsIso (underlyingLowerShriekComparison R U) := sorry

end SheafOfModules.Localization
