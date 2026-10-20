/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Stalk
import StacksCheckRecall

/-!
# Remark 18.38.2

Compatibility facade for the failure of a localization-direct-image stalk formula analogous to
localization lower shriek.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w z

namespace SheafOfModules.Localization.directImage

/- Remark 18.38.2 (0711): the coproduct decomposition of localization lower-shriek stalks has no
uniform analogue for localization direct image `j_{U,*}`. -/
@[stacks 0711]
#check
  (@not_forall_underlyingFiber_isomorphic_coproduct.{u, v, w, z} :
    ¬ ∀ {C : Type u} [Category.{v} C] [HasBinaryProducts C]
        {J : GrothendieckTopology C} [LocallySmall.{z} C]
        (R : Sheaf J RingCat.{w}) (U : C)
        (p : J.Point.{z})
        (G : SheafOfModules.{z} (R.over U)),
      IsIsomorphic
        (((directImage R U) ⋙ toSheaf R ⋙ p.sheafFiber).obj G)
        (∐ fun x : p.fiber.obj U ↦
          ((toSheaf (R.over U) ⋙ (p.over x).sheafFiber).obj G)))

end SheafOfModules.Localization.directImage
