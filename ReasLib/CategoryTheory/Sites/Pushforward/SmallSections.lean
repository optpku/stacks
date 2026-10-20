/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.KanExtension.SmallSections
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Sheaf direct image from small compatible sections

The right Kan construction is needed only for sheaves in this interface.
Each object's actual comma-diagram sections supply its size condition;
no assertion of right Kan extensions for every presheaf is required.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe uC vC uD vD w

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- The particular pointwise extension of a sheaf remains a sheaf by cover lifting. -/
theorem pointwiseRightKanExtension_isSheaf
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsCocontinuous J K]
    {A : Type*} [Category* A] (F : Sheaf J A)
    [G.op.HasPointwiseRightKanExtension F.obj] :
    Presheaf.IsSheaf K (pointwiseRightKanExtension G.op F.obj) := by
  rw [Presheaf.isSheaf_iff_multifork]
  intro Y S
  exact ⟨RanIsSheafOfIsCocontinuous.isLimitMultifork F.property
    (pointwiseRightKanExtensionIsPointwiseRightKanExtension G.op F.obj) S⟩

/-- Type-valued sheaf direct image with a size condition only on genuine sheaf sections. -/
def sheafPushforwardOfSmallSections
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsCocontinuous J K]
    [∀ F : Sheaf J (Type w), ∀ Y : Dᵒᵖ,
      Small.{w} (StructuredArrow.proj Y G.op ⋙ F.obj).sections] :
    Sheaf J (Type w) ⥤ Sheaf K (Type w) where
  obj F := ⟨pointwiseRightKanExtension G.op F.obj,
    pointwiseRightKanExtension_isSheaf G J K F⟩
  map {F F'} η := ObjectProperty.homMk
    ((pointwiseRightKanExtension G.op F'.obj).liftOfIsRightKanExtension
      (pointwiseRightKanExtensionCounit G.op F'.obj)
      (pointwiseRightKanExtension G.op F.obj)
      (pointwiseRightKanExtensionCounit G.op F.obj ≫ η.hom))
  map_id := sorry
  map_comp := sorry

/-- Ring-valued sheaf direct image uses the actual native compatible-section ring limits. -/
def sheafPushforwardRingOfSmallSections
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsCocontinuous J K]
    [∀ F : Sheaf J RingCat.{w}, ∀ Y : Dᵒᵖ,
      Small.{w} ((StructuredArrow.proj Y G.op ⋙ F.obj) ⋙ forget RingCat.{w}).sections] :
    Sheaf J RingCat.{w} ⥤ Sheaf K RingCat.{w} where
  obj F := ⟨pointwiseRightKanExtension G.op F.obj,
    pointwiseRightKanExtension_isSheaf G J K F⟩
  map {F F'} η := ObjectProperty.homMk
    ((pointwiseRightKanExtension G.op F'.obj).liftOfIsRightKanExtension
      (pointwiseRightKanExtensionCounit G.op F'.obj)
      (pointwiseRightKanExtension G.op F.obj)
      (pointwiseRightKanExtensionCounit G.op F.obj ≫ η.hom))
  map_id := sorry
  map_comp := sorry

end CategoryTheory.Functor
