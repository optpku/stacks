/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Functor.RightKanExtension.Composition

/-!
# Functoriality of presheaf pullback and pushforward along 1-morphisms

For composable 1-morphisms of categories fibred in groupoids over `(Sch/S)_fppf`,
presheaf pullback is strictly functorial and presheaf pushforward is functorial
up to the canonical right Kan extension comparison isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Presheaf pullback along a composite of morphisms of groupoid fibrations equals
the composite of the individual pullback functors. -/
theorem presheafPullback_comp :
    (whiskeringLeft X.totalᵒᵖ Z.totalᵒᵖ (Type (u + 1))).obj (toFunctor (f ≫ g)).op =
      (whiskeringLeft Y.totalᵒᵖ Z.totalᵒᵖ (Type (u + 1))).obj (toFunctor g).op ⋙
        (whiskeringLeft X.totalᵒᵖ Y.totalᵒᵖ (Type (u + 1))).obj (toFunctor f).op :=
  sorry

/-- The canonical isomorphism from presheaf pushforward along a composite of
morphisms of groupoid fibrations to the composite of their pushforward functors. -/
def presheafPushforwardCompIso :
    ((toFunctor (f ≫ g)).op.ran :
      (X.totalᵒᵖ ⥤ Type (u + 1)) ⥤ (Z.totalᵒᵖ ⥤ Type (u + 1))) ≅
      ((toFunctor f).op.ran ⋙ (toFunctor g).op.ran :
        (X.totalᵒᵖ ⥤ Type (u + 1)) ⥤ (Z.totalᵒᵖ ⥤ Type (u + 1))) :=
  ranCompIso (toFunctor f).op (toFunctor g).op

/-- Compatibility of `presheafPushforwardCompIso` with the adjunctions
`(f^p, _p f)`, `(g^p, _p g)`, and `((g ∘ f)^p, _p(g ∘ f))`. -/
theorem presheafPushforwardCompIso_homEquiv
    {H : Z.totalᵒᵖ ⥤ Type (u + 1)} {F : X.totalᵒᵖ ⥤ Type (u + 1)}
    (α : ((whiskeringLeft X.totalᵒᵖ Z.totalᵒᵖ (Type (u + 1))).obj
      (toFunctor (f ≫ g)).op).obj H ⟶ F) :
    ((toFunctor (f ≫ g)).op.ranAdjunction (Type (u + 1))).homEquiv H F α ≫
        (presheafPushforwardCompIso f g).hom.app F =
      ((toFunctor f).op.ranCompAdjunction (toFunctor g).op).homEquiv H F α :=
  sorry

end AlgebraicGeometry

end
