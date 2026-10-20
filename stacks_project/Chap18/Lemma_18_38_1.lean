/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Stalk
import StacksCheckRecall

/-!
# Lemma 18.38.1

Compatibility facade for the stalk decomposition of localization lower shriek.  The
coefficient-general decomposition and the module-forgetful bridge are owned by ReasLib.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w z

namespace SheafOfModules.Localization.lowerShriek

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{z} C]
variable (R : Sheaf J RingCat.{w}) (U : C)
variable [(restriction R U : SheafOfModules.{z} R ⥤
  SheafOfModules.{z} (R.over U)).IsRightAdjoint]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [∀ P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{z},
  (Over.forget U).op.HasLeftKanExtension P]
variable (p : J.Point.{z})
variable (G : SheafOfModules.{z} (R.over U))

/- Lemma 18.38.1 (0710), bridge: taking the stalk of the canonical mate compares additive
localization lower shriek with the additive sheaf underlying module lower shriek. -/
@[stacks 0710 "underlying comparison"]
#check
  (underlyingFiberComparison R U p G :
    p.sheafFiber.obj
        (((Over.forget U).sheafPullback AddCommGrpCat.{z} (J.over U) J).obj
          ((toSheaf (R.over U)).obj G)) ⟶
      p.sheafFiber.obj
        ((toSheaf R).obj ((lowerShriek R U).obj G)))

/- Lemma 18.38.1 (0710): the underlying additive stalk of `j_{U!} G` is the coproduct of the
stalks of `G` at the localized points `p.over x`, indexed by `x : p.fiber.obj U`. -/
@[stacks 0710]
#check
  (underlyingFiber_isomorphic_coproduct R U p G :
    IsIsomorphic
      (((lowerShriek R U) ⋙ toSheaf R ⋙ p.sheafFiber).obj G)
      (∐ fun x : p.fiber.obj U ↦
        ((toSheaf (R.over U) ⋙ (p.over x).sheafFiber).obj G)))

end SheafOfModules.Localization.lowerShriek
