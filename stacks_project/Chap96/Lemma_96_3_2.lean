module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Lemma_96_3_2_Comparison

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

/-- Lemma 96.3.2 (1): Let `f : X ⟶ Y` and `g : Y ⟶ Z` be 1-morphisms of
categories fibred in groupoids over `(Sch/S)_fppf`. Then
`(g ∘ f)^p = f^p ∘ g^p`, i.e. precomposition with `(toFunctor (f ≫ g)).op`
equals the composite of precomposition with `(toFunctor g).op` and
precomposition with `(toFunctor f).op`. -/
@[stacks 06TL]
theorem presheafPullback_comp :
    (whiskeringLeft X.totalᵒᵖ Z.totalᵒᵖ (Type (u + 1))).obj (toFunctor (f ≫ g)).op =
      (whiskeringLeft Y.totalᵒᵖ Z.totalᵒᵖ (Type (u + 1))).obj (toFunctor g).op ⋙
        (whiskeringLeft X.totalᵒᵖ Y.totalᵒᵖ (Type (u + 1))).obj (toFunctor f).op :=
  sorry

/-- Lemma 96.3.2 (2): There is a canonical isomorphism
`_p(g ∘ f) ⟶ _p g ∘ _p f`, i.e.
`(toFunctor (f ≫ g)).op.ran ≅ (toFunctor f).op.ran ⋙ (toFunctor g).op.ran`,
compatible with adjointness of `(f^p, _p f)`, `(g^p, _p g)`, and
`((g ∘ f)^p, _p(g ∘ f))`. -/
@[stacks 06TL]
def presheafPushforwardCompIso :
    ((toFunctor (f ≫ g)).op.ran :
      (X.totalᵒᵖ ⥤ Type (u + 1)) ⥤ (Z.totalᵒᵖ ⥤ Type (u + 1))) ≅
      ((toFunctor f).op.ran ⋙ (toFunctor g).op.ran :
        (X.totalᵒᵖ ⥤ Type (u + 1)) ⥤ (Z.totalᵒᵖ ⥤ Type (u + 1))) :=
  ranCompIso (toFunctor f).op (toFunctor g).op

/-- `presheafPushforwardCompIso` is the right Kan extension composition isomorphism
along the opposite total functors of `f` and `g`. -/
theorem presheafPushforwardCompIso_eq :
    presheafPushforwardCompIso f g = ranCompIso (toFunctor f).op (toFunctor g).op :=
  sorry

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
