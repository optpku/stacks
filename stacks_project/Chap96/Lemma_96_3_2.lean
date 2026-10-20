module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.PresheafComposition
import StacksCheckRecall

/-!
# Functoriality of presheaf pullback and pushforward along 1-morphisms

For composable 1-morphisms of categories fibred in groupoids over `(Sch/S)_fppf`,
presheaf pullback is strictly functorial and presheaf pushforward is functorial
up to a canonical isomorphism compatible with adjunctions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 96.3.2. Presheaf pullback along a composite equals the composite of
pullbacks; pushforward has the canonical composition isomorphism below,
compatible with the individual and composite adjunctions. -/
@[stacks 06TL] #check (AlgebraicGeometry.presheafPullback_comp f g :
  (whiskeringLeft X.totalᵒᵖ Z.totalᵒᵖ (Type (u + 1))).obj (toFunctor (f ≫ g)).op =
    (whiskeringLeft Y.totalᵒᵖ Z.totalᵒᵖ (Type (u + 1))).obj (toFunctor g).op ⋙
      (whiskeringLeft X.totalᵒᵖ Y.totalᵒᵖ (Type (u + 1))).obj (toFunctor f).op)

#check (AlgebraicGeometry.presheafPushforwardCompIso f g :
  ((toFunctor (f ≫ g)).op.ran :
    (X.totalᵒᵖ ⥤ Type (u + 1)) ⥤ (Z.totalᵒᵖ ⥤ Type (u + 1))) ≅
    ((toFunctor f).op.ran ⋙ (toFunctor g).op.ran :
      (X.totalᵒᵖ ⥤ Type (u + 1)) ⥤ (Z.totalᵒᵖ ⥤ Type (u + 1))))

#check (AlgebraicGeometry.presheafPushforwardCompIso_homEquiv f g :
  ∀ {H : Z.totalᵒᵖ ⥤ Type (u + 1)} {F : X.totalᵒᵖ ⥤ Type (u + 1)}
    (α : ((whiskeringLeft X.totalᵒᵖ Z.totalᵒᵖ (Type (u + 1))).obj
      (toFunctor (f ≫ g)).op).obj H ⟶ F),
    ((toFunctor (f ≫ g)).op.ranAdjunction (Type (u + 1))).homEquiv H F α ≫
        (presheafPushforwardCompIso f g).hom.app F =
      ((toFunctor f).op.ranCompAdjunction (toFunctor g).op).homEquiv H F α)

end
