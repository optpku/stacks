/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
import StacksCheckRecall

/-!
# Remark 18.41.2

Compatibility facade for the mate comparing additive and module lower shriek.  ReasLib owns the
comparison itself, the localization criterion, and the fact that invertibility is not automatic.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ u₂ v₁ v₂ w z

namespace RingedSite.Cocontinuous

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
variable (R : Sheaf K RingCat.{w})

section Comparison

variable [HasWeakSheafify K AddCommGrpCat.{z}]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P]

/- Remark 18.41.2 (0798): taking the mate of the strict forgetful right-adjoint square gives the
canonical comparison from additive lower shriek after forgetting to the underlying sheaf of
module lower shriek. -/
@[stacks 0798 "forgetful comparison"]
#check (moduleLowerShriek.underlyingComparison (J := J) (K := K) f R :
  SheafOfModules.toSheaf
      (inverseImageRingSheaf (J := J) (K := K) f R) ⋙
      f.sheafPullback AddCommGrpCat.{z} J K ⟶
    moduleLowerShriek (J := J) (K := K) f R ⋙
      SheafOfModules.toSheaf R)

end Comparison

section Criterion

variable [HasWeakSheafify K AddCommGrpCat.{w}]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, f.op.HasLeftKanExtension P]
variable [∀ U : C, HasWeakSheafify (K.over (f.obj U)) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{w},
  (Over.post f).op.HasLeftKanExtension P]

/- Remark 18.41.2 (0798): the forgetful comparison is invertible exactly when every localized
structure-sheaf comparison from Equation 18.41.2.1 is invertible. -/
@[stacks 0798 "localization criterion"]
#check (moduleLowerShriek.underlyingComparison_isIso_iff
  (J := J) (K := K) f R :
    IsIso (moduleLowerShriek.underlyingComparison (J := J) (K := K) f R) ↔
      ∀ U : C, IsIso (Localization.structureSheafComparison
        (J := J) (K := K) f R U))

end Criterion

/- Remark 18.41.2 (0798): this comparison is not uniformly invertible. -/
@[stacks 0798 "nonautomatic"]
#check (moduleLowerShriek.not_all_underlyingComparison_isIso :
  ¬ ∀ {C : Type u₁} [Category.{v₁} C]
      {D : Type u₂} [Category.{v₂} D]
      {J : GrothendieckTopology C} {K : GrothendieckTopology D}
      (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
      (R : Sheaf K RingCat.{w})
      [HasWeakSheafify K AddCommGrpCat.{z}]
      [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P],
    IsIso (moduleLowerShriek.underlyingComparison
      (J := J) (K := K) f R))

end RingedSite.Cocontinuous
