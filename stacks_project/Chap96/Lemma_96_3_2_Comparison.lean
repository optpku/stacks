/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.RightKanExtension.Composition

/-!
# Composition of right Kan extensions

The composed adjunction, canonical comparison isomorphism, and its compatibility
with adjunction hom-equivalences are provided by the shared composition API.
-/

@[expose] public section

noncomputable section

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open CategoryTheory CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {H : Type u₄} [Category.{v₄} H]
variable (L : C ⥤ D) (K : D ⥤ E)
variable [∀ F : C ⥤ H, L.HasRightKanExtension F]
variable [∀ F : D ⥤ H, K.HasRightKanExtension F]

#check (CategoryTheory.Functor.ranCompAdjunction L K :
  (whiskeringLeft C E H).obj (L ⋙ K) ⊣ L.ran ⋙ K.ran)

variable [∀ F : C ⥤ H, (L ⋙ K).HasRightKanExtension F]

#check (CategoryTheory.Functor.ranCompIso L K :
  ((L ⋙ K).ran : (C ⥤ H) ⥤ (E ⥤ H)) ≅
    (L.ran ⋙ K.ran : (C ⥤ H) ⥤ (E ⥤ H)))

#check (CategoryTheory.Functor.ranCompIso_homEquiv L K :
  ∀ {F : E ⥤ H} {G : C ⥤ H}
    (α : ((whiskeringLeft C E H).obj (L ⋙ K)).obj F ⟶ G),
    ((L ⋙ K).ranAdjunction H).homEquiv F G α ≫ (L.ranCompIso K).hom.app G =
      (L.ranCompAdjunction K).homEquiv F G α)

end
