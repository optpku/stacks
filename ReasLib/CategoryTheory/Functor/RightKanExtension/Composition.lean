/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Composition of right Kan extensions

For composable functors `L : C ⥤ D` and `K : D ⥤ E`, uniqueness of right adjoints
supplies a canonical isomorphism `(L ⋙ K).ran ≅ L.ran ⋙ K.ran`.
-/

@[expose] public section

noncomputable section

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {H : Type u₄} [Category.{v₄} H]
variable (L : C ⥤ D) (K : D ⥤ E)
variable [∀ F : C ⥤ H, L.HasRightKanExtension F]
variable [∀ F : D ⥤ H, K.HasRightKanExtension F]

/-- The composed adjunction whose left adjoint is precomposition with `L ⋙ K` and
whose right adjoint is `L.ran ⋙ K.ran`. -/
def ranCompAdjunction :
    (whiskeringLeft C E H).obj (L ⋙ K) ⊣ L.ran ⋙ K.ran :=
  (K.ranAdjunction H).comp (L.ranAdjunction H)

variable [∀ F : C ⥤ H, (L ⋙ K).HasRightKanExtension F]

/-- The canonical isomorphism `(L ⋙ K).ran ≅ L.ran ⋙ K.ran`, with forward map
from the composite right Kan extension to the composite of the individual
right Kan extensions. -/
def ranCompIso :
    ((L ⋙ K).ran : (C ⥤ H) ⥤ (E ⥤ H)) ≅
      (L.ran ⋙ K.ran : (C ⥤ H) ⥤ (E ⥤ H)) :=
  ((L ⋙ K).ranAdjunction H).rightAdjointUniq (L.ranCompAdjunction K)

/-- Compatibility of `ranCompIso` with the hom-equivalences of
`(L ⋙ K).ranAdjunction` and `ranCompAdjunction`. -/
theorem ranCompIso_homEquiv {F : E ⥤ H} {G : C ⥤ H}
    (α : ((whiskeringLeft C E H).obj (L ⋙ K)).obj F ⟶ G) :
    ((L ⋙ K).ranAdjunction H).homEquiv F G α ≫ (L.ranCompIso K).hom.app G =
      (L.ranCompAdjunction K).homEquiv F G α :=
  sorry

end CategoryTheory.Functor

end
