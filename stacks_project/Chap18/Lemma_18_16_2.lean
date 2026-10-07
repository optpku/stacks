module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek.Basic
import StacksCheckRecall

/-!
# Lemma 18.16.2

The presheaf and sheaf lower-shriek functors are the canonical left adjoints to restriction and
continuous direct image, respectively.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D)

section Presheaf

variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension P]

variable (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (𝒢 : Dᵒᵖ ⥤ AddCommGrpCat.{w})

/- Lemma 18.16.2 (1) (04BG): presheaf lower shriek is left adjoint to restriction. -/
@[stacks 04BG "(1)"]
#check (((u.op.lanAdjunction AddCommGrpCat.{w}).homEquiv ℱ 𝒢) :
  ((u.op.lan).obj ℱ ⟶ 𝒢) ≃ (ℱ ⟶ u.op ⋙ 𝒢))

end Presheaf

section Sheaf

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify K AddCommGrpCat.{w}]
variable (ℱ : Sheaf J AddCommGrpCat.{w}) (𝒢 : Sheaf K AddCommGrpCat.{w})

/- Lemma 18.16.2 (2) (04BG): sheaf lower shriek is left adjoint to continuous direct image. -/
@[stacks 04BG "(2)"]
#check (((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv ℱ 𝒢) :
  ((u.sheafPullback AddCommGrpCat.{w} J K).obj ℱ ⟶ 𝒢) ≃
    (ℱ ⟶ (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj 𝒢))

end Sheaf

end CategoryTheory
