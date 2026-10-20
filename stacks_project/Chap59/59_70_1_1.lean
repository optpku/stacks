/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Over.ExtensionByZero
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C]

/- 59.70.1.1: the presheaf extension by zero on the étale site has value at
`V` given by the direct sum of `F(V ⟶ U)` over arrows `V ⟶ U`. -/
@[stacks 0F4K]
#check
  (CategoryTheory.Over.Forget.LeftKanExtension.extensionByZeroCoproductMap_isIso :
    ∀ (U : C) (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{max u v w})
      [((Over.forget U).op).HasPointwiseLeftKanExtension F]
      (V : C),
      IsIso
        (CategoryTheory.Over.Forget.LeftKanExtension.extensionByZeroCoproductMap U F V))
