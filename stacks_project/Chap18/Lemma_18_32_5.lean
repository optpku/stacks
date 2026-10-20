/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible.Small
import StacksCheckRecall

/-!
# Lemma 18.32.5

The mathematical owner is the generic representative-set theorem for an essentially small,
isomorphism-closed object property.  ReasLib supplies essential smallness of the invertible-module
property at the natural module-category universe.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (O : Sheaf J CommRingCat.{max u v})
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Lemma 18.32.5 (040B): invertible module sheaves admit a set containing exactly one
representative of each isomorphism class. -/
@[stacks 040B]
#check
  (ObjectProperty.EssentiallySmall.exists_set_representatives
    (MonoidalCategory.isInvertibleObject (C := ringedSiteModuleCategory J O)) :
    ∃ S : Set (ringedSiteModuleCategory J O),
      (∀ L ∈ S, MonoidalCategory.isInvertibleObject L) ∧
      ∀ L : ringedSiteModuleCategory J O,
        MonoidalCategory.isInvertibleObject L →
          ∃! N : ringedSiteModuleCategory J O, N ∈ S ∧ Nonempty (N ≅ L))

end SheafOfModules.RingedSite
