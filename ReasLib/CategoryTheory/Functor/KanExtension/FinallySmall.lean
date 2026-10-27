/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.FinallySmall

/-! # Pointwise left extensions from finally small comma categories

The data bundle is Mathlib's `LeftExtension`; its functor and unit are the
native pointwise colimit construction. Category universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w uC uD uH vC vD vH

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} {H : Type uH}
  [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]

/-- Obtain the pointwise colimits from a final-small model of each full comma. -/
theorem hasPointwiseLeftKanExtensionOfFinallySmall
    (L : C ⥤ D) (F : C ⥤ H) [HasColimitsOfSize.{w, w} H]
    (hfinally : ∀ Y : D, FinallySmall.{w} (CostructuredArrow L Y)) :
    L.HasPointwiseLeftKanExtension F := by
  intro Y
  letI : FinallySmall.{w} (CostructuredArrow L Y) := hfinally Y
  letI : HasColimitsOfShape (CostructuredArrow L Y) H :=
    Limits.hasColimitsOfShape_of_finallySmall (CostructuredArrow L Y) H
  infer_instance

/-- The actual pointwise extension functor and its canonical colimit-injection unit. -/
noncomputable def pointwiseLeftExtensionOfFinallySmall
    (L : C ⥤ D) (F : C ⥤ H) [HasColimitsOfSize.{w, w} H]
    (hfinally : ∀ Y : D, FinallySmall.{w} (CostructuredArrow L Y)) :
    LeftExtension L F := by
  letI := hasPointwiseLeftKanExtensionOfFinallySmall L F hfinally
  exact LeftExtension.mk (pointwiseLeftKanExtension L F)
    (pointwiseLeftKanExtensionUnit L F)

/-- The displayed native functor and unit have the left Kan universal property. -/
theorem pointwiseLeftExtensionOfFinallySmall_isLeftKanExtension
    (L : C ⥤ D) (F : C ⥤ H) [HasColimitsOfSize.{w, w} H]
    (hfinally : ∀ Y : D, FinallySmall.{w} (CostructuredArrow L Y)) :
    (pointwiseLeftExtensionOfFinallySmall L F hfinally).right.IsLeftKanExtension
      (pointwiseLeftExtensionOfFinallySmall L F hfinally).hom := by
  letI := hasPointwiseLeftKanExtensionOfFinallySmall L F hfinally
  change (pointwiseLeftKanExtension L F).IsLeftKanExtension
    (pointwiseLeftKanExtensionUnit L F)
  infer_instance

end CategoryTheory.Functor
