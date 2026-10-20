/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Underlying
public import ReasLib.CategoryTheory.Sites.Point.Localization.LowerShriek
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of localization lower shriek for module sheaves

The stalk decomposition itself belongs to the coefficient-general point-localization API.
This file supplies the thin bridge for module sheaves: first forget module structure through the
canonical mate comparison, then apply the additive lower-shriek decomposition.  It also records
the corresponding failure for localization direct image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

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

namespace lowerShriek

/-- The explicit stalkwise mate comparison from additive localization lower shriek to the
underlying additive sheaf of module localization lower shriek. -/
@[stacks 0710 "underlying comparison"]
noncomputable def underlyingFiberComparison
    (p : J.Point.{z})
    (G : SheafOfModules.{z} (R.over U)) :
    p.sheafFiber.obj
        (((Over.forget U).sheafPullback AddCommGrpCat.{z} (J.over U) J).obj
          ((toSheaf (R.over U)).obj G)) ⟶
      p.sheafFiber.obj
        ((toSheaf R).obj ((lowerShriek R U).obj G)) :=
  p.sheafFiber.map ((underlyingLowerShriekComparison R U).app G)

/-- The stalkwise underlying lower-shriek comparison is invertible. -/
@[stacks 0710 "underlying comparison isomorphism", instance]
theorem underlyingFiberComparison_isIso
    (p : J.Point.{z})
    (G : SheafOfModules.{z} (R.over U)) :
    IsIso (underlyingFiberComparison R U p G) := sorry

variable [LocallySmall.{z} C]

/-- After forgetting module structure, the stalk at `p` of localization
lower shriek is isomorphic to the coproduct of the stalks at the localized points `p.over x`.
The coefficient rings of the summands vary with `x`, so the canonical common target is
`AddCommGrpCat`. -/
@[stacks 0710]
theorem underlyingFiber_isomorphic_coproduct
    (p : J.Point.{z})
    (G : SheafOfModules.{z} (R.over U)) :
    IsIsomorphic
      (((lowerShriek R U) ⋙ toSheaf R ⋙ p.sheafFiber).obj G)
      (∐ fun x : p.fiber.obj U ↦
        ((toSheaf (R.over U) ⋙ (p.over x).sheafFiber).obj G)) := sorry

end lowerShriek

namespace directImage

/-- Localization direct image of module sheaves admits no uniform
coproduct formula over the localized points analogous to localization lower shriek. -/
@[stacks 0711]
theorem not_forall_underlyingFiber_isomorphic_coproduct :
    ¬ ∀ {C : Type u} [Category.{v} C] [HasBinaryProducts C]
        {J : GrothendieckTopology C} [LocallySmall.{z} C]
        (R : Sheaf J RingCat.{w}) (U : C)
        (p : J.Point.{z})
        (G : SheafOfModules.{z} (R.over U)),
      IsIsomorphic
        (((directImage R U) ⋙ toSheaf R ⋙ p.sheafFiber).obj G)
        (∐ fun x : p.fiber.obj U ↦
          ((toSheaf (R.over U) ⋙ (p.over x).sheafFiber).obj G)) := sorry

end directImage

end SheafOfModules.Localization
