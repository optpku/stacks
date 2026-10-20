/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
import StacksCheckRecall

/-!
# Remark 18.19.7

Compatibility facade for localization of presheaves of modules.  The reusable owner exposes both
adjoints of restriction, an explicit coproduct map computing lower shriek, and exactness; the
sheaf owner supplies the associated-sheaf comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace PresheafOfModules.Localization

variable {C : Type u} [SmallCategory C]
variable (R : Cᵒᵖ ⥤ RingCat.{u}) (U : C)

/- Remark 18.19.7 (1): presheaf lower shriek is left adjoint to restriction to `C / U`. -/
@[stacks 03EJ "(1)"]
#check
  (lowerShriekRestrictionAdj R U :
    lowerShriek R U ⊣ restriction R U)

/- Remark 18.19.7 (2): presheaf direct image is right adjoint to restriction. -/
@[stacks 03EJ "(2)"]
#check
  (restrictionDirectImageAdj R U :
    restriction R U ⊣ directImage R U)

variable (G : PresheafOfModules ((Over.forget U).op ⋙ R)) (V : C)

/- Remark 18.19.7 (3): the explicit coproduct map indexed by arrows `V ⟶ U` computes the
value at `V` of presheaf lower shriek. -/
@[stacks 03EJ "(3)"]
#check
  (coproductToLowerShriek_isIso R U G V :
    IsIso (coproductToLowerShriek R U G V))

/- Remark 18.19.7 (4): presheaf lower shriek is exact. -/
@[stacks 03EJ "(4)"]
#check
  (lowerShriek_exact R U :
    exactFunctor _ _ (lowerShriek R U))

end PresheafOfModules.Localization

namespace SheafOfModules.Localization

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J RingCat.{u}) (U : C)

/- Remark 18.19.7 (5): sheaf lower shriek is the associated sheaf of the presheaf lower-shriek
construction after forgetting the sheaf condition. -/
@[stacks 03EJ "(5)"]
#check
  (lowerShriekSheafificationIso R U :
    (lowerShriek R U :
      SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R) ≅
      lowerShriekSheafification R U)

end SheafOfModules.Localization
