/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Lemma_96_3_3_Pullback
public import stacks_project.Chap96.Lemma_96_3_3_Pushforward
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# 2-morphisms of categories fibred in groupoids act on presheaves

A 2-morphism `t : f ⟶ g` of categories fibred in groupoids over `(Sch/S)_fppf`
induces canonical isomorphisms `t^p : g^p ≅ f^p` and `_p t : _p f ≅ _p g`,
compatible with adjointness and with vertical and horizontal composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Opposite
open FiberedCategoryOver.Groupoids (toFunctor toNatTrans)
open scoped Bicategory

noncomputable section

universe u w

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- Lemma 96.3.3 (1): a 2-morphism `t : f ⟶ g` of categories fibred in groupoids
over `(Sch/S)_fppf` induces a canonical isomorphism `t^p : g^p ≅ f^p` of
presheaf pullbacks. -/
@[stacks 06TM]
def presheafInverseImageIso {X Y : GroupoidsOver S} {f g : X ⟶ Y} (t : f ⟶ g) :
    presheafInverseImage (toFunctor g) (Type w) ≅
      presheafInverseImage (toFunctor f) (Type w) :=
  FiberedCategoryOver.Groupoids.presheafInverseImageIso t

/-- `presheafInverseImageIso t` is the inverse-image isomorphism assigned to the
underlying total-functor isomorphism of `t`. -/
theorem presheafInverseImageIso_eq {X Y : GroupoidsOver S} {f g : X ⟶ Y}
    (t : f ⟶ g) :
    presheafInverseImageIso t =
      FiberedCategoryOver.Groupoids.presheafInverseImageIso t :=
  sorry

/-- On a presheaf `𝒢`, the components of `t^p` are `𝒢.map ((toNatTrans t).app x).op`. -/
theorem presheafInverseImageIso_hom_app {X Y : GroupoidsOver S} {f g : X ⟶ Y}
    (t : f ⟶ g) (𝒢 : Y.totalᵒᵖ ⥤ Type w) (x : X.total) :
    ((presheafInverseImageIso t).hom.app 𝒢).app (op x) =
      𝒢.map ((toNatTrans t).app x).op :=
  sorry

/-- Lemma 96.3.3 (2): the same 2-morphism induces a canonical isomorphism
`_p t : _p f ≅ _p g` of presheaf pushforwards. -/
@[stacks 06TM]
def presheafRanIso {X Y : GroupoidsOver S} {f g : X ⟶ Y} (t : f ⟶ g)
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor g).op F] :
    ((toFunctor f).op.ran : (X.totalᵒᵖ ⥤ Type w) ⥤ (Y.totalᵒᵖ ⥤ Type w)) ≅
      ((toFunctor g).op.ran : (X.totalᵒᵖ ⥤ Type w) ⥤ (Y.totalᵒᵖ ⥤ Type w)) :=
  FiberedCategoryOver.Groupoids.presheafRanIso t

/-- `presheafRanIso t` is the conjugate of `t^p` along the two `ranAdjunction`s. -/
theorem presheafRanIso_eq {X Y : GroupoidsOver S} {f g : X ⟶ Y} (t : f ⟶ g)
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor g).op F] :
    presheafRanIso t = FiberedCategoryOver.Groupoids.presheafRanIso t :=
  sorry

/-- Lemma 96.3.3 (3): `t^p` and `_p t` are compatible with adjointness of
`(f^p ⊣ _p f)` and `(g^p ⊣ _p g)`. -/
@[stacks 06TM]
theorem presheafRanIso_homEquiv {X Y : GroupoidsOver S} {f g : X ⟶ Y} (t : f ⟶ g)
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor g).op F]
    (𝒢 : Y.totalᵒᵖ ⥤ Type w) (ℱ : X.totalᵒᵖ ⥤ Type w)
    (α : (presheafInverseImage (toFunctor f) (Type w)).obj 𝒢 ⟶ ℱ) :
    ((toFunctor g).op.ranAdjunction (Type w)).homEquiv 𝒢 ℱ
        ((presheafInverseImageIso t).hom.app 𝒢 ≫ α) =
      ((toFunctor f).op.ranAdjunction (Type w)).homEquiv 𝒢 ℱ α ≫
        (presheafRanIso t).hom.app ℱ :=
  sorry

/-- Lemma 96.3.3 (4): `t^p` is compatible with vertical composition of
2-morphisms. -/
@[stacks 06TM]
theorem presheafInverseImageIso_comp {X Y : GroupoidsOver S} {f g h : X ⟶ Y}
    (t : f ⟶ g) (s : g ⟶ h) :
    presheafInverseImageIso (t ≫ s) =
      presheafInverseImageIso s ≪≫ presheafInverseImageIso t :=
  sorry

/-- Lemma 96.3.3 (5): `_p t` is compatible with vertical composition of
2-morphisms. -/
@[stacks 06TM]
theorem presheafRanIso_comp {X Y : GroupoidsOver S} {f g h : X ⟶ Y}
    (t : f ⟶ g) (s : g ⟶ h)
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor g).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor h).op F] :
    presheafRanIso (t ≫ s) = presheafRanIso t ≪≫ presheafRanIso s :=
  sorry

/-- Lemma 96.3.3 (6): `t^p` is compatible with left Bicategory whiskering of
2-morphisms. -/
@[stacks 06TM]
theorem presheafInverseImageIso_whiskerLeft {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) {p q : Y ⟶ Z} (σ : p ⟶ q) :
    presheafInverseImageIso (f ◁ σ) =
      FiberedCategoryOver.Groupoids.presheafInverseImage_compIso f q (Type w) ≪≫
        isoWhiskerRight (presheafInverseImageIso σ)
          (presheafInverseImage (toFunctor f) (Type w)) ≪≫
        (FiberedCategoryOver.Groupoids.presheafInverseImage_compIso f p
          (Type w)).symm :=
  sorry

/-- Lemma 96.3.3 (7): `t^p` is compatible with right Bicategory whiskering of
2-morphisms. -/
@[stacks 06TM]
theorem presheafInverseImageIso_whiskerRight {X Y Z : GroupoidsOver S}
    {f g : X ⟶ Y} (t : f ⟶ g) (p : Y ⟶ Z) :
    presheafInverseImageIso (t ▷ p) =
      FiberedCategoryOver.Groupoids.presheafInverseImage_compIso g p (Type w) ≪≫
        isoWhiskerLeft (presheafInverseImage (toFunctor p) (Type w))
          (presheafInverseImageIso t) ≪≫
        (FiberedCategoryOver.Groupoids.presheafInverseImage_compIso f p
          (Type w)).symm :=
  sorry

/-- Lemma 96.3.3 (8): `_p t` is compatible with left Bicategory whiskering of
2-morphisms. -/
@[stacks 06TM]
theorem presheafRanIso_whiskerLeft {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) {p q : Y ⟶ Z} (σ : p ⟶ q)
    [UnivLE.{u + 1, w}]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op F]
    [∀ F : Y.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor p).op F]
    [∀ F : Y.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor q).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      HasRightKanExtension ((toFunctor f).op ⋙ (toFunctor p).op) F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      HasRightKanExtension ((toFunctor f).op ⋙ (toFunctor q).op) F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor (f ≫ p)).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor (f ≫ q)).op F] :
    presheafRanIso (f ◁ σ) =
      FiberedCategoryOver.Groupoids.presheafRanCompIso f p ≪≫
        isoWhiskerLeft ((toFunctor f).op.ran) (presheafRanIso σ) ≪≫
        (FiberedCategoryOver.Groupoids.presheafRanCompIso f q).symm :=
  sorry

/-- Lemma 96.3.3 (9): `_p t` is compatible with right Bicategory whiskering of
2-morphisms. -/
@[stacks 06TM]
theorem presheafRanIso_whiskerRight {X Y Z : GroupoidsOver S}
    {f g : X ⟶ Y} (t : f ⟶ g) (p : Y ⟶ Z)
    [UnivLE.{u + 1, w}]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor g).op F]
    [∀ F : Y.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor p).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      HasRightKanExtension ((toFunctor f).op ⋙ (toFunctor p).op) F]
    [∀ F : X.totalᵒᵖ ⥤ Type w,
      HasRightKanExtension ((toFunctor g).op ⋙ (toFunctor p).op) F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor (f ≫ p)).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor (g ≫ p)).op F] :
    presheafRanIso (t ▷ p) =
      FiberedCategoryOver.Groupoids.presheafRanCompIso f p ≪≫
        isoWhiskerRight (presheafRanIso t) (toFunctor p).op.ran ≪≫
        (FiberedCategoryOver.Groupoids.presheafRanCompIso g p).symm :=
  sorry

end AlgebraicGeometry

end
