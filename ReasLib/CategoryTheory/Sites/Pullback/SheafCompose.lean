/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Pullback and direct image through coefficient functors

This leaf records the coefficient-functor comparisons for the canonical
direct and inverse image functors on sheaves.  The comparison is independent
of a concrete presentation of the coefficients, so it is formulated for an
arbitrary functor `F : A ⥤ B` rather than only for an underlying-set functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ u₂ v₁ v₂ w₁ w₂ a b

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type w₁} [Category.{a} A]
variable {B : Type w₂} [Category.{b} B]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace sheafPushforwardContinuous

/-- Continuous sheaf direct image commutes definitionally with postcomposition
by a coefficient functor preserving sheaves on both sites. -/
@[simp]
theorem compSheafCompose
    (u : C ⥤ D) (F : A ⥤ B) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [J.HasSheafCompose F] [K.HasSheafCompose F] :
    u.sheafPushforwardContinuous A J K ⋙ sheafCompose J F =
      sheafCompose K F ⋙ u.sheafPushforwardContinuous B J K := sorry

end sheafPushforwardContinuous

namespace sheafPullbackConstruction

/-- The explicit left-Kan-extension-and-sheafification construction of inverse
image commutes with postcomposition by a coefficient functor. -/
noncomputable def compSheafComposeIso
    (u : C ⥤ D) (F : A ⥤ B) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ B, u.op.HasLeftKanExtension P]
    [F.PreservesLeftKanExtensions u.op]
    [HasWeakSheafify K A] [HasWeakSheafify K B]
    [J.HasSheafCompose F] [K.HasSheafCompose F] [K.PreservesSheafification F] :
    sheafPullback u A J K ⋙ sheafCompose K F ≅
      sheafCompose J F ⋙ sheafPullback u B J K :=
  (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (sheafToPresheaf J A)
        (Functor.associator _ _ _ ≪≫
          isoWhiskerLeft u.op.lan
            (sheafComposeNatIso K F (sheafificationAdjunction K A)
              (sheafificationAdjunction K B)).symm)) ≪≫
    isoWhiskerLeft (sheafToPresheaf J A)
      ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (F.lanCompIsoOfPreserves u.op)
          (presheafToSheaf K B) ≪≫
        Functor.associator _ _ _) ≪≫
    Iso.refl _

end sheafPullbackConstruction

namespace sheafPullback

/-- The canonical sheaf inverse image commutes with postcomposition by a
coefficient functor under the Kan-extension and sheafification comparison
hypotheses. -/
noncomputable def compSheafComposeIso
    (u : C ⥤ D) (F : A ⥤ B) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ B, u.op.HasLeftKanExtension P]
    [F.PreservesLeftKanExtensions u.op]
    [HasWeakSheafify K A] [HasWeakSheafify K B]
    [J.HasSheafCompose F] [K.HasSheafCompose F] [K.PreservesSheafification F] :
    u.sheafPullback A J K ⋙ sheafCompose K F ≅
      sheafCompose J F ⋙ u.sheafPullback B J K :=
  isoWhiskerRight (sheafPullbackConstruction.sheafPullbackIso u A J K) (sheafCompose K F) ≪≫
    sheafPullbackConstruction.compSheafComposeIso u F J K ≪≫
    isoWhiskerLeft (sheafCompose J F)
      (sheafPullbackConstruction.sheafPullbackIso u B J K).symm

end sheafPullback

end CategoryTheory.Functor
