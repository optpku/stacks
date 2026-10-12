/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
import StacksCheckRecall

/-!
# Equation 18.41.2.1

Compatibility facade for the localized structure-sheaf comparison.  Its localized unit objects,
right-adjoint map, and adjoint transpose are owned by ReasLib.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace RingedSite.Cocontinuous.Localization

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f : C ⥤ D) [f.IsContinuous J K]
variable (R : Sheaf K RingCat.{w}) (U : C)
variable [HasWeakSheafify (K.over (f.obj U)) AddCommGrpCat.{w}]
variable [∀ P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{w},
  (Over.post f).op.HasLeftKanExtension P]

/- Equation 18.41.2.1 (0799): additive lower shriek on the localized sites carries the
inverse-image structure sheaf to the target localized structure sheaf by this canonical map. -/
@[stacks 0799]
#check (structureSheafComparison (J := J) (K := K) f R U :
  ((Over.post f).sheafPullback AddCommGrpCat.{w}
      (J.over U) (K.over (f.obj U))).obj
      (SheafOfModules.Localization.unitUnderlying
        (RingedSite.Cocontinuous.inverseImageRingSheaf
          (J := J) (K := K) f R) U) ⟶
    SheafOfModules.Localization.unitUnderlying R (f.obj U))

/- The same comparison in right-adjoint form, before transposing across localized lower shriek. -/
#check (structureSheafRightAdjointMap (J := J) (K := K) f R U)

end RingedSite.Cocontinuous.Localization
