/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import ReasLib.CategoryTheory.Sites.Over
import StacksCheckRecall

/-!
# Lemma 18.19.8

The hypothesis that arrows into `U` are unique is used as explicit bundled evidence that
`Over.forget U` is fully faithful.  The two conclusions are then direct specializations of the
generic unit/counit API for fully faithful functors of sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (U : C)
variable (hU : ∀ X : C, Subsingleton (X ⟶ U))
variable (F : Sheaf (J.over U) AddCommGrpCat.{w})

section LowerShriek

variable [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [∀ P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{w},
  (Over.forget U).op.HasLeftKanExtension P]
variable [(Over.forget U).op.HasPointwiseLeftKanExtension F.obj]
variable [∀ P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{w},
  (Over.forget U).op.HasPointwiseRightKanExtension P]

/- Lemma 18.19.8 (1): the unit `F ⟶ j_U⁻¹ j_{U!} F` is invertible. -/
@[stacks 0F6Z "(1)"]
#check
  (Functor.FullyFaithful.sheafAdjunctionContinuous_unit_app_isIso
      (J.over U) J (Over.forget U)
      (Over.forgetFullyFaithfulOfSubsingletonHom U hU) F :
    IsIso
      (((Over.forget U).sheafAdjunctionContinuous
        AddCommGrpCat.{w} (J.over U) J).unit.app F))

end LowerShriek

section DirectImage

variable [∀ P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{w},
  (Over.forget U).op.HasPointwiseRightKanExtension P]

/- Lemma 18.19.8 (2): the counit `j_U⁻¹ j_{U*} F ⟶ F` is invertible. -/
@[stacks 0F6Z "(2)"]
#check
  (Functor.FullyFaithful.sheafAdjunctionCocontinuous_counit_app_isIso
      (J.over U) J (Over.forget U)
      (Over.forgetFullyFaithfulOfSubsingletonHom U hU) F :
    IsIso
      (((Over.forget U).sheafAdjunctionCocontinuous
        AddCommGrpCat.{w} (J.over U) J).counit.app F))

end DirectImage

end CategoryTheory
