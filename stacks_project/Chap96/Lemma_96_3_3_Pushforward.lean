/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Lemma_96_3_3_Pullback
public import stacks_project.Chap96.Lemma_96_3_2_Comparison
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Presheaf pushforward isomorphisms as mates of inverse-image isomorphisms

The comparison `_p t` is the conjugate of `t^p` along the two right
Kan-extension adjunctions.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory

universe u v uX vX w

namespace CategoryTheory.FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]
variable {X Y Z : FiberedCategoryOver.Groupoids.{u, v, uX, vX} C}

noncomputable section

/-- The presheaf pushforward isomorphism `_p t : _p f ≅ _p g` assigned to a
2-morphism `t : f ⟶ g`, realized as the mate of `t^p` along the two
`ranAdjunction`s. -/
def presheafRanIso {f g : X ⟶ Y} (t : f ⟶ g)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor g).op F] :
    ((toFunctor f).op.ran : (X.totalᵒᵖ ⥤ Type w) ⥤ (Y.totalᵒᵖ ⥤ Type w)) ≅
      ((toFunctor g).op.ran : (X.totalᵒᵖ ⥤ Type w) ⥤ (Y.totalᵒᵖ ⥤ Type w)) :=
  conjugateIsoEquiv
    ((toFunctor f).op.ranAdjunction (Type w))
    ((toFunctor g).op.ranAdjunction (Type w))
    (presheafInverseImageIso t)

/-- `_p t` is the conjugate isomorphism of `t^p` along the two presheaf
right Kan-extension adjunctions. -/
theorem presheafRanIso_conjugate {f g : X ⟶ Y} (t : f ⟶ g)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor g).op F] :
    presheafRanIso t =
      conjugateIsoEquiv
        ((toFunctor f).op.ranAdjunction (Type w))
        ((toFunctor g).op.ranAdjunction (Type w))
        (presheafInverseImageIso t) :=
  sorry

/-- Compatibility of `t^p` and `_p t` with the adjunctions `(f^p ⊣ _p f)` and
`(g^p ⊣ _p g)`: precomposition with `t^p` corresponds to postcomposition with
`_p t` under `ranAdjunction.homEquiv`. -/
theorem presheafRanIso_homEquiv {f g : X ⟶ Y} (t : f ⟶ g)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor g).op F]
    (𝒢 : Y.totalᵒᵖ ⥤ Type w) (ℱ : X.totalᵒᵖ ⥤ Type w)
    (α : (Functor.presheafInverseImage (toFunctor f) (Type w)).obj 𝒢 ⟶ ℱ) :
    ((toFunctor g).op.ranAdjunction (Type w)).homEquiv 𝒢 ℱ
        ((presheafInverseImageIso t).hom.app 𝒢 ≫ α) =
      ((toFunctor f).op.ranAdjunction (Type w)).homEquiv 𝒢 ℱ α ≫
        (presheafRanIso t).hom.app ℱ :=
  sorry

/-- Vertical composition of 2-morphisms is preserved by `_p t`. -/
theorem presheafRanIso_comp {f g h : X ⟶ Y} (t : f ⟶ g) (s : g ⟶ h)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor g).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor h).op F] :
    presheafRanIso (t ≫ s) = presheafRanIso t ≪≫ presheafRanIso s :=
  sorry

/-- Comparison of pushforward along a composite 1-morphism with the composite of
the individual pushforwards, obtained by conjugating
`presheafInverseImage_compIso` and then applying `ranCompIso`. -/
def presheafRanCompIso (f : X ⟶ Y) (h : Y ⟶ Z)
    [UnivLE.{max uX vX, w}]
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : Y.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor h).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension ((toFunctor f).op ⋙ (toFunctor h).op) F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension (toFunctor (f ≫ h)).op F] :
    ((toFunctor (f ≫ h)).op.ran :
      (X.totalᵒᵖ ⥤ Type w) ⥤ (Z.totalᵒᵖ ⥤ Type w)) ≅
      ((toFunctor f).op.ran ⋙ (toFunctor h).op.ran :
        (X.totalᵒᵖ ⥤ Type w) ⥤ (Z.totalᵒᵖ ⥤ Type w)) :=
  (conjugateIsoEquiv
      (((toFunctor f).op ⋙ (toFunctor h).op).ranAdjunction (Type w))
      ((toFunctor (f ≫ h)).op.ranAdjunction (Type w))
      (presheafInverseImage_compIso f h (Type w))).symm ≪≫
    Functor.ranCompIso (toFunctor f).op (toFunctor h).op

/-- `presheafRanCompIso` is the conjugate of `presheafInverseImage_compIso`
followed by the right Kan extension composition isomorphism. -/
theorem presheafRanCompIso_eq (f : X ⟶ Y) (h : Y ⟶ Z)
    [UnivLE.{max uX vX, w}]
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : Y.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor h).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension ((toFunctor f).op ⋙ (toFunctor h).op) F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension (toFunctor (f ≫ h)).op F] :
    presheafRanCompIso f h =
      (conjugateIsoEquiv
          (((toFunctor f).op ⋙ (toFunctor h).op).ranAdjunction (Type w))
          ((toFunctor (f ≫ h)).op.ranAdjunction (Type w))
          (presheafInverseImage_compIso f h (Type w))).symm ≪≫
        Functor.ranCompIso (toFunctor f).op (toFunctor h).op :=
  sorry

/-- Left Bicategory whiskering of a 2-morphism is compatible with `_p t` after
the total-functor composition comparison and `ranCompIso`. -/
theorem presheafRanIso_whiskerLeft (f : X ⟶ Y) {h k : Y ⟶ Z} (s : h ⟶ k)
    [UnivLE.{max uX vX, w}]
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : Y.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor h).op F]
    [∀ F : Y.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor k).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension ((toFunctor f).op ⋙ (toFunctor h).op) F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension ((toFunctor f).op ⋙ (toFunctor k).op) F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension (toFunctor (f ≫ h)).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension (toFunctor (f ≫ k)).op F] :
    presheafRanIso (f ◁ s) =
      presheafRanCompIso f h ≪≫
        Functor.isoWhiskerLeft ((toFunctor f).op.ran) (presheafRanIso s) ≪≫
        (presheafRanCompIso f k).symm :=
  sorry

/-- Right Bicategory whiskering of a 2-morphism is compatible with `_p t` after
the total-functor composition comparison and `ranCompIso`. -/
theorem presheafRanIso_whiskerRight {f g : X ⟶ Y} (t : f ⟶ g) (h : Y ⟶ Z)
    [UnivLE.{max uX vX, w}]
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor g).op F]
    [∀ F : Y.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor h).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension ((toFunctor f).op ⋙ (toFunctor h).op) F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension ((toFunctor g).op ⋙ (toFunctor h).op) F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension (toFunctor (f ≫ h)).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension (toFunctor (g ≫ h)).op F] :
    presheafRanIso (t ▷ h) =
      presheafRanCompIso f h ≪≫
        Functor.isoWhiskerRight (presheafRanIso t) (toFunctor h).op.ran ≪≫
        (presheafRanCompIso g h).symm :=
  sorry

end

end CategoryTheory.FiberedCategoryOver.Groupoids

