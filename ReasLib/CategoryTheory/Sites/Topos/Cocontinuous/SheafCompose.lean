module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-!
# Cocontinuous direct image through coefficient functors

This leaf compares cocontinuous sheaf direct image with postcomposition by a coefficient
functor.  The only coefficient-specific hypothesis is preservation of the relevant right Kan
extensions, so the comparison applies uniformly to forgetful functors which create limits.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ u₂ v₁ v₂ w₁ w₂ a b

namespace CategoryTheory.Functor.sheafPushforwardCocontinuous

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type w₁} [Category.{a} A]
variable {B : Type w₂} [Category.{b} B]
variable (u : C ⥤ D) (F : A ⥤ B)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsCocontinuous J K]
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ B, u.op.HasPointwiseRightKanExtension P]
variable [F.PreservesRightKanExtensions u.op]
variable [J.HasSheafCompose F] [K.HasSheafCompose F]

/-- Cocontinuous sheaf direct image commutes with a coefficient functor which preserves the
right Kan extensions defining direct image. -/
noncomputable def compSheafComposeIso :
    u.sheafPushforwardCocontinuous A J K ⋙ sheafCompose K F ≅
      sheafCompose J F ⋙ u.sheafPushforwardCocontinuous B J K :=
  let uPushA := u.sheafPushforwardCocontinuous A J K
  let uPushB := u.sheafPushforwardCocontinuous B J K
  let postcompose := (whiskeringRight Dᵒᵖ A B).obj F
  let ranIso :
      (u.op.ran : (Cᵒᵖ ⥤ A) ⥤ Dᵒᵖ ⥤ A) ⋙ postcompose ≅
        (whiskeringRight Cᵒᵖ A B).obj F ⋙
          (u.op.ran : (Cᵒᵖ ⥤ B) ⥤ Dᵒᵖ ⥤ B) :=
    CategoryTheory.Functor.ranCompIsoOfPreserves
      (A := Cᵒᵖ) (B := A) (C := Dᵒᵖ) (D := B) F u.op
  let presheafIso :
      (uPushA ⋙ sheafCompose K F) ⋙ sheafToPresheaf K B ≅
        (sheafCompose J F ⋙ uPushB) ⋙ sheafToPresheaf K B :=
    calc
      (uPushA ⋙ sheafCompose K F) ⋙ sheafToPresheaf K B ≅
          uPushA ⋙ (sheafCompose K F ⋙ sheafToPresheaf K B) :=
        Functor.associator _ _ _
      _ ≅ uPushA ⋙ (sheafToPresheaf K A ⋙
          (whiskeringRight Dᵒᵖ A B).obj F) := Iso.refl _
      _ ≅ (uPushA ⋙ sheafToPresheaf K A) ⋙
          (whiskeringRight Dᵒᵖ A B).obj F :=
        (Functor.associator _ _ _).symm
      _ ≅ (sheafToPresheaf J A ⋙ u.op.ran) ⋙
          (whiskeringRight Dᵒᵖ A B).obj F :=
        isoWhiskerRight
          (u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K) _
      _ ≅ sheafToPresheaf J A ⋙
          (u.op.ran ⋙ (whiskeringRight Dᵒᵖ A B).obj F) :=
        Functor.associator _ _ _
      _ ≅ sheafToPresheaf J A ⋙
          ((whiskeringRight Cᵒᵖ A B).obj F ⋙ u.op.ran) :=
        isoWhiskerLeft _ ranIso
      _ ≅ (sheafToPresheaf J A ⋙
          (whiskeringRight Cᵒᵖ A B).obj F) ⋙ u.op.ran :=
        (Functor.associator _ _ _).symm
      _ ≅ (sheafCompose J F ⋙ sheafToPresheaf J B) ⋙ u.op.ran :=
        Iso.refl _
      _ ≅ sheafCompose J F ⋙ (sheafToPresheaf J B ⋙ u.op.ran) :=
        Functor.associator _ _ _
      _ ≅ sheafCompose J F ⋙ (uPushB ⋙ sheafToPresheaf K B) :=
        isoWhiskerLeft _
          (u.sheafPushforwardCocontinuousCompSheafToPresheafIso B J K).symm
      _ ≅ (sheafCompose J F ⋙ uPushB) ⋙ sheafToPresheaf K B :=
        (Functor.associator _ _ _).symm
  Functor.fullyFaithfulCancelRight (sheafToPresheaf K B) presheafIso

-- The comparison is assembled from the canonical right-Kan-extension comparison and fully
-- faithful cancellation; it contains no chosen coefficient-level inverse data.

end CategoryTheory.Functor.sheafPushforwardCocontinuous
