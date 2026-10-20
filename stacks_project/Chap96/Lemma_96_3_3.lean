module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Presheaf.Pullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Presheaf.Pushforward
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
import StacksCheckRecall

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

/- Lemma 96.3.3 (1): a 2-morphism `t : f ⟶ g` of categories fibred in groupoids
over `(Sch/S)_fppf` induces a canonical isomorphism `t^p : g^p ≅ f^p` of
presheaf pullbacks. -/
@[stacks 06TM] #check (CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso :
  ∀ {X Y : GroupoidsOver S} {f g : X ⟶ Y} (t : f ⟶ g),
    presheafInverseImage (toFunctor g) (Type w) ≅
      presheafInverseImage (toFunctor f) (Type w))

/- On a presheaf `𝒢`, the components of `t^p` are `𝒢.map ((toNatTrans t).app x).op`. -/
#check (CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso_hom_app :
  ∀ {X Y : GroupoidsOver S} {f g : X ⟶ Y}
    (t : f ⟶ g) (𝒢 : Y.totalᵒᵖ ⥤ Type w) (x : X.total),
    ((CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso t).hom.app 𝒢).app (op x) =
      𝒢.map ((toNatTrans t).app x).op)

/- Lemma 96.3.3 (2): the same 2-morphism induces a canonical isomorphism
`_p t : _p f ≅ _p g` of presheaf pushforwards. -/
@[stacks 06TM] #check (CategoryTheory.FiberedCategoryOver.Groupoids.presheafRanIso :
  ∀ {X Y : GroupoidsOver S} {f g : X ⟶ Y} (t : f ⟶ g)
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor g).op F],
    ((toFunctor f).op.ran : (X.totalᵒᵖ ⥤ Type w) ⥤ (Y.totalᵒᵖ ⥤ Type w)) ≅
      ((toFunctor g).op.ran : (X.totalᵒᵖ ⥤ Type w) ⥤ (Y.totalᵒᵖ ⥤ Type w)))

/- Lemma 96.3.3 (3): `t^p` and `_p t` are compatible with adjointness of
`(f^p ⊣ _p f)` and `(g^p ⊣ _p g)`. -/
@[stacks 06TM] #check (CategoryTheory.FiberedCategoryOver.Groupoids.presheafRanIso_homEquiv :
  ∀ {X Y : GroupoidsOver S} {f g : X ⟶ Y} (t : f ⟶ g)
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor g).op F]
    (𝒢 : Y.totalᵒᵖ ⥤ Type w) (ℱ : X.totalᵒᵖ ⥤ Type w)
    (α : (presheafInverseImage (toFunctor f) (Type w)).obj 𝒢 ⟶ ℱ),
    ((toFunctor g).op.ranAdjunction (Type w)).homEquiv 𝒢 ℱ
        ((CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso t).hom.app 𝒢 ≫ α) =
      ((toFunctor f).op.ranAdjunction (Type w)).homEquiv 𝒢 ℱ α ≫
        (CategoryTheory.FiberedCategoryOver.Groupoids.presheafRanIso t).hom.app ℱ)

/- Lemma 96.3.3 (4): `t^p` is compatible with vertical composition of
2-morphisms. -/
@[stacks 06TM] #check (CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso_comp :
  ∀ {X Y : GroupoidsOver S} {f g h : X ⟶ Y}
    (t : f ⟶ g) (s : g ⟶ h),
    CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso (t ≫ s) =
      CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso s ≪≫ CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso t)

/- Lemma 96.3.3 (5): `_p t` is compatible with vertical composition of
2-morphisms. -/
@[stacks 06TM] #check (CategoryTheory.FiberedCategoryOver.Groupoids.presheafRanIso_comp :
  ∀ {X Y : GroupoidsOver S} {f g h : X ⟶ Y}
    (t : f ⟶ g) (s : g ⟶ h)
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor g).op F]
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor h).op F],
    CategoryTheory.FiberedCategoryOver.Groupoids.presheafRanIso (t ≫ s) = CategoryTheory.FiberedCategoryOver.Groupoids.presheafRanIso t ≪≫ CategoryTheory.FiberedCategoryOver.Groupoids.presheafRanIso s)

/- Lemma 96.3.3 (6): `t^p` is compatible with left Bicategory whiskering of
2-morphisms. -/
@[stacks 06TM] #check (CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso_whiskerLeft :
  ∀ {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) {p q : Y ⟶ Z} (σ : p ⟶ q),
    CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso (f ◁ σ) =
      FiberedCategoryOver.Groupoids.presheafInverseImage_compIso f q (Type w) ≪≫
        isoWhiskerRight (CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso σ)
          (presheafInverseImage (toFunctor f) (Type w)) ≪≫
        (FiberedCategoryOver.Groupoids.presheafInverseImage_compIso f p
          (Type w)).symm)

/- Lemma 96.3.3 (7): `t^p` is compatible with right Bicategory whiskering of
2-morphisms. -/
@[stacks 06TM] #check (CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso_whiskerRight :
  ∀ {X Y Z : GroupoidsOver S}
    {f g : X ⟶ Y} (t : f ⟶ g) (p : Y ⟶ Z),
    CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso (t ▷ p) =
      FiberedCategoryOver.Groupoids.presheafInverseImage_compIso g p (Type w) ≪≫
        isoWhiskerLeft (presheafInverseImage (toFunctor p) (Type w))
          (CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImageIso t) ≪≫
        (FiberedCategoryOver.Groupoids.presheafInverseImage_compIso f p
          (Type w)).symm)

/- Lemma 96.3.3 (8): `_p t` is compatible with left Bicategory whiskering of
2-morphisms. -/
@[stacks 06TM] #check (CategoryTheory.FiberedCategoryOver.Groupoids.presheafRanIso_whiskerLeft :
  ∀ {X Y Z : GroupoidsOver S}
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
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor (f ≫ q)).op F],
    CategoryTheory.FiberedCategoryOver.Groupoids.presheafRanIso (f ◁ σ) =
      FiberedCategoryOver.Groupoids.presheafRanCompIso f p ≪≫
        isoWhiskerLeft ((toFunctor f).op.ran) (CategoryTheory.FiberedCategoryOver.Groupoids.presheafRanIso σ) ≪≫
        (FiberedCategoryOver.Groupoids.presheafRanCompIso f q).symm)

/- Lemma 96.3.3 (9): `_p t` is compatible with right Bicategory whiskering of
2-morphisms. -/
@[stacks 06TM] #check (CategoryTheory.FiberedCategoryOver.Groupoids.presheafRanIso_whiskerRight :
  ∀ {X Y Z : GroupoidsOver S}
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
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor (g ≫ p)).op F],
    CategoryTheory.FiberedCategoryOver.Groupoids.presheafRanIso (t ▷ p) =
      FiberedCategoryOver.Groupoids.presheafRanCompIso f p ≪≫
        isoWhiskerRight (CategoryTheory.FiberedCategoryOver.Groupoids.presheafRanIso t) (toFunctor p).op.ran ≪≫
        (FiberedCategoryOver.Groupoids.presheafRanCompIso g p).symm)

end AlgebraicGeometry

end
