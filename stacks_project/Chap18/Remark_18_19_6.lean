/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Underlying
import StacksCheckRecall

/-!
# Remark 18.19.6

Compatibility facade for the mate comparison expressing that localization lower shriek commutes
with forgetting module structure.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{w}) (U : C)
variable [(restriction R U : SheafOfModules.{z} R ⥤
  SheafOfModules.{z} (R.over U)).IsRightAdjoint]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [∀ P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{z},
  (Over.forget U).op.HasLeftKanExtension P]

/- Remark 18.19.6 (08P4): the canonical mate from additive lower shriek to the additive sheaf
underlying module lower shriek is invertible. -/
@[stacks 08P4]
#check
  (underlyingLowerShriekComparison_isIso R U :
    IsIso (underlyingLowerShriekComparison R U))

end SheafOfModules.Localization
