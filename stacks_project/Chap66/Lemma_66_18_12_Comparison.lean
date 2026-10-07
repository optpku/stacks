module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward

/-!
# Base-change comparison for étale restriction of small étale sheaves

A cartesian square of algebraic spaces with étale bottom edge induces a canonical
morphism `(f_small,* ℱ)|_{Y'} ⟶ f'_small,* (ℱ|_{X'})` of sheaves on `Y'_étale`, and
the matching comparison of higher direct images and of inverse images.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Functor
open Opposite

noncomputable section

universe u v w

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.RightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImageEtaleBaseChangeHom`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

variable {X' X Y' Y : AlgebraicSpace S}
variable {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Postcomposition of small étale restriction with base change is continuous. -/
instance etaleRestriction_comp_etaleBaseChange_isContinuous
    {X Y Z : AlgebraicSpace S} (e : X ⟶ Y) (φ : Z ⟶ Y) [Etale e] :
    (etaleRestriction e ⋙ etaleBaseChange φ).IsContinuous
      (smallEtaleTopology X) (spacesEtaleTopology Z) :=
  Functor.isContinuous_comp (etaleRestriction e) (etaleBaseChange φ)
    (smallEtaleTopology X) (smallEtaleTopology Y) (spacesEtaleTopology Z)

/-- Base change followed by spaces étale restriction is continuous. -/
instance etaleBaseChange_comp_spacesEtaleRestriction_isContinuous
    {X Y Z : AlgebraicSpace S} (e : X ⟶ Y) (φ : X ⟶ Z) [Etale e] :
    (etaleBaseChange φ ⋙ spacesEtaleRestriction e).IsContinuous
      (smallEtaleTopology Z) (spacesEtaleTopology Y) :=
  Functor.isContinuous_comp (etaleBaseChange φ) (spacesEtaleRestriction e)
    (smallEtaleTopology Z) (spacesEtaleTopology X) (spacesEtaleTopology Y)

/-- Small étale restriction followed by the spaces inclusion is continuous. -/
instance etaleRestriction_comp_smallEtaleInclusion_isContinuous
    {X Y : AlgebraicSpace S} (e : X ⟶ Y) [Etale e] :
    (etaleRestriction e ⋙ smallEtaleInclusion Y).IsContinuous
      (smallEtaleTopology X) (spacesEtaleTopology Y) :=
  Functor.isContinuous_comp (etaleRestriction e) (smallEtaleInclusion Y)
    (smallEtaleTopology X) (smallEtaleTopology Y) (spacesEtaleTopology Y)

/-- The spaces inclusion followed by spaces étale restriction is continuous. -/
instance smallEtaleInclusion_comp_spacesEtaleRestriction_isContinuous
    {X Y : AlgebraicSpace S} (e : X ⟶ Y) [Etale e] :
    (smallEtaleInclusion X ⋙ spacesEtaleRestriction e).IsContinuous
      (smallEtaleTopology X) (spacesEtaleTopology Y) :=
  Functor.isContinuous_comp (smallEtaleInclusion X) (spacesEtaleRestriction e)
    (smallEtaleTopology X) (spacesEtaleTopology X) (spacesEtaleTopology Y)

/-- The functor-of-points map `X' ×_{Y'} V' ⟶ X ×_Y V'` induced by a cartesian square. -/
def etaleBaseChangeRestrictMapNat (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
    (V' : smallEtaleSite Y') :
    etaleBaseChangeFunctorOfPoints f' V' ⟶
      etaleBaseChangeFunctorOfPoints f ((etaleRestriction g).obj V') :=
  pullback.map (homFunctor f') (homFunctor V'.hom) (homFunctor f)
    (homFunctor ((etaleRestriction g).obj V').hom) h (𝟙 _) g h_cart.w.symm
    (Category.id_comp _).symm

/-- The morphism of algebraic spaces étale over `X` comparing the two fibre products of a
cartesian square. -/
def etaleBaseChangeRestrictMap (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
    (V' : smallEtaleSite Y') :
    (spacesEtaleRestriction h).obj ((etaleBaseChange f').obj V') ⟶
      (etaleBaseChange f).obj ((etaleRestriction g).obj V') :=
  MorphismProperty.Over.homMk (etaleBaseChangeRestrictMapNat h_cart V') sorry

/-- The site-level natural transformation comparing fibre products along a cartesian square
with étale bottom edge. -/
def etaleBaseChangeRestrictNatTrans (h_cart : IsPullback h f' f g) [Etale g] [Etale h] :
    etaleBaseChange f' ⋙ spacesEtaleRestriction h ⟶
      etaleRestriction g ⋙ etaleBaseChange f where
  app := etaleBaseChangeRestrictMap h_cart
  naturality := sorry

/-- Continuous sheaf pushforward of the fibre-product comparison of a cartesian square. -/
def etaleBaseChangeRestrictSheafHom (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
    (A : Type v) [Category.{w} A] :
    (etaleRestriction g ⋙ etaleBaseChange f).sheafPushforwardContinuous A
        (smallEtaleTopology Y') (spacesEtaleTopology X) ⟶
      (etaleBaseChange f' ⋙ spacesEtaleRestriction h).sheafPushforwardContinuous A
        (smallEtaleTopology Y') (spacesEtaleTopology X) :=
  sheafPushforwardContinuousNatTrans (etaleBaseChangeRestrictNatTrans h_cart) A
    (smallEtaleTopology Y') (spacesEtaleTopology X)

/-- The 2-cell of sheaf restriction functors associated to the commuting square of small and
spaces étale restriction. -/
def etaleRestrictionInclusionTwoSquare {U V : AlgebraicSpace S} (φ : U ⟶ V) [Etale φ]
    (A : Type v) [Category.{w} A] :
    TwoSquare
      ((spacesEtaleRestriction φ).sheafPushforwardContinuous A
        (spacesEtaleTopology U) (spacesEtaleTopology V))
      ((smallEtaleInclusion V).sheafPushforwardContinuous A
        (smallEtaleTopology V) (spacesEtaleTopology V))
      ((smallEtaleInclusion U).sheafPushforwardContinuous A
        (smallEtaleTopology U) (spacesEtaleTopology U))
      ((etaleRestriction φ).sheafPushforwardContinuous A
        (smallEtaleTopology U) (smallEtaleTopology V)) :=
  TwoSquare.mk _ _ _ _
    ((sheafPushforwardContinuousIso (etaleRestriction_comp_inclusion φ).symm A
        (smallEtaleTopology U) (spacesEtaleTopology V)).hom)

/-- Beck–Chevalley morphism swapping small-étale extension with étale restriction, obtained as
the mate of `etaleRestrictionInclusionTwoSquare`. -/
def restrictionExtensionMate {U V : AlgebraicSpace S} (φ : U ⟶ V) [Etale φ]
    (A : Type v) [Category.{w} A]
    [∀ P : (smallEtaleSite V)ᵒᵖ ⥤ A,
      (smallEtaleInclusion V).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallEtaleSite U)ᵒᵖ ⥤ A,
      (smallEtaleInclusion U).op.HasPointwiseRightKanExtension P] :
    (smallEtaleInclusion V).sheafPushforwardCocontinuous A
          (smallEtaleTopology V) (spacesEtaleTopology V) ⋙
        (spacesEtaleRestriction φ).sheafPushforwardContinuous A
          (spacesEtaleTopology U) (spacesEtaleTopology V) ⟶
      (etaleRestriction φ).sheafPushforwardContinuous A
          (smallEtaleTopology U) (smallEtaleTopology V) ⋙
        (smallEtaleInclusion U).sheafPushforwardCocontinuous A
          (smallEtaleTopology U) (spacesEtaleTopology U) :=
  (mateEquiv
      ((smallEtaleInclusion V).sheafAdjunctionCocontinuous A
        (smallEtaleTopology V) (spacesEtaleTopology V))
      ((smallEtaleInclusion U).sheafAdjunctionCocontinuous A
        (smallEtaleTopology U) (spacesEtaleTopology U))
      (etaleRestrictionInclusionTwoSquare φ A)).natTrans

/-- The canonical base-change morphism
`(f_small,* ℱ)|_{Y'} ⟶ f'_small,* (ℱ|_{X'})` as a natural transformation of functors. -/
def pushforwardEtaleBaseChangeNatTrans (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
    (A : Type v) [Category.{w} A]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallEtaleSite X')ᵒᵖ ⥤ A,
      (smallEtaleInclusion X').op.HasPointwiseRightKanExtension P] :
    sheafPushforward A f ⋙ etaleRestrictionSheaf g A ⟶
      etaleRestrictionSheaf h A ⋙ sheafPushforward A f' :=
  whiskerLeft
      ((smallEtaleInclusion X).sheafPushforwardCocontinuous A
        (smallEtaleTopology X) (spacesEtaleTopology X))
      (etaleBaseChangeRestrictSheafHom h_cart A) ≫
    whiskerRight (restrictionExtensionMate h A)
      ((etaleBaseChange f').sheafPushforwardContinuous A
        (smallEtaleTopology Y') (spacesEtaleTopology X'))

/-- The canonical base-change morphism
`(f_small,* ℱ)|_{Y'} ⟶ f'_small,* (ℱ|_{X'})` of sheaves on `Y'_étale`. -/
def pushforwardEtaleBaseChangeHom (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
    (A : Type v) [Category.{w} A]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallEtaleSite X')ᵒᵖ ⥤ A,
      (smallEtaleInclusion X').op.HasPointwiseRightKanExtension P]
    (F : Sheaf (smallEtaleTopology X) A) :
    (etaleRestrictionSheaf g A).obj ((sheafPushforward A f).obj F) ⟶
      (sheafPushforward A f').obj ((etaleRestrictionSheaf h A).obj F) :=
  (pushforwardEtaleBaseChangeNatTrans h_cart A).app F

/-- The canonical higher-direct-image base-change morphism
`(R^i f_small,* ℱ)|_{Y'} ⟶ R^i f'_small,* (ℱ|_{X'})`. -/
def higherDirectImageEtaleBaseChangeHom (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y') AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]
    [(sheafPushforward AddCommGrpCat.{u + 1} f).Additive]
    [(sheafPushforward AddCommGrpCat.{u + 1} f').Additive]
    [(etaleRestrictionSheaf g AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf h AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf g AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf h AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf h AddCommGrpCat.{u + 1}).PreservesInjectiveObjects]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (i : ℕ) :
    (etaleRestrictionSheaf g AddCommGrpCat.{u + 1}).obj (higherDirectImage f F i) ⟶
      higherDirectImage f' ((etaleRestrictionSheaf h AddCommGrpCat.{u + 1}).obj F) i :=
  (Functor.RightDerived.postcompIso (sheafPushforward AddCommGrpCat.{u + 1} f)
        (etaleRestrictionSheaf g AddCommGrpCat.{u + 1}) i).inv.app F ≫
    (NatTrans.rightDerived (pushforwardEtaleBaseChangeNatTrans h_cart
        AddCommGrpCat.{u + 1}) i).app F ≫
      (Functor.RightDerived.precompIso (etaleRestrictionSheaf h AddCommGrpCat.{u + 1})
          (sheafPushforward AddCommGrpCat.{u + 1} f') i).hom.app F

/-- The mate of the fibre-product comparison along the pullback⊣pushforward adjunctions of
`etaleBaseChange`. -/
def inverseImageSpacesEtaleRestrictNatTrans (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
    (A : Type v) [Category.{w} A]
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ A, (etaleBaseChange f).op.HasLeftKanExtension F]
    [∀ F : (smallEtaleSite Y')ᵒᵖ ⥤ A, (etaleBaseChange f').op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) A]
    [HasWeakSheafify (spacesEtaleTopology X') A] :
    etaleRestrictionSheaf g A ⋙
        Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f') A
          (smallEtaleTopology Y') (spacesEtaleTopology X') ⟶
      Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) A
          (smallEtaleTopology Y) (spacesEtaleTopology X) ⋙
        (spacesEtaleRestriction h).sheafPushforwardContinuous A
          (spacesEtaleTopology X') (spacesEtaleTopology X) :=
  ((mateEquiv
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (etaleBaseChange f) A
          (smallEtaleTopology Y) (spacesEtaleTopology X))
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (etaleBaseChange f') A
          (smallEtaleTopology Y') (spacesEtaleTopology X'))).symm
      (TwoSquare.mk
        ((etaleBaseChange f).sheafPushforwardContinuous A
          (smallEtaleTopology Y) (spacesEtaleTopology X))
        ((spacesEtaleRestriction h).sheafPushforwardContinuous A
          (spacesEtaleTopology X') (spacesEtaleTopology X))
        (etaleRestrictionSheaf g A)
        ((etaleBaseChange f').sheafPushforwardContinuous A
          (smallEtaleTopology Y') (spacesEtaleTopology X'))
        (etaleBaseChangeRestrictSheafHom h_cart A))).natTrans

/-- The canonical inverse-image comparison
`(f')_small^{-1}(𝒢|_{Y'}) ⟶ (f_small^{-1} 𝒢)|_{X'}` of the cartesian square. -/
def inverseImageEtaleRestrictHom (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
    (A : Type v) [Category.{w} A]
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ A, (etaleBaseChange f).op.HasLeftKanExtension F]
    [∀ F : (smallEtaleSite Y')ᵒᵖ ⥤ A, (etaleBaseChange f').op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) A]
    [HasWeakSheafify (spacesEtaleTopology X') A]
    (G : Sheaf (smallEtaleTopology Y) A) :
    (sheafInverseImage A f').obj ((etaleRestrictionSheaf g A).obj G) ⟶
      (etaleRestrictionSheaf h A).obj ((sheafInverseImage A f).obj G) :=
  ((associator (etaleRestrictionSheaf g A)
        (Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f') A
          (smallEtaleTopology Y') (spacesEtaleTopology X'))
        ((smallEtaleInclusion X').sheafPushforwardContinuous A
          (smallEtaleTopology X') (spacesEtaleTopology X'))).inv ≫
    whiskerRight (inverseImageSpacesEtaleRestrictNatTrans h_cart A)
      ((smallEtaleInclusion X').sheafPushforwardContinuous A
        (smallEtaleTopology X') (spacesEtaleTopology X')) ≫
      (associator
          (Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) A
            (smallEtaleTopology Y) (spacesEtaleTopology X))
          ((spacesEtaleRestriction h).sheafPushforwardContinuous A
            (spacesEtaleTopology X') (spacesEtaleTopology X))
          ((smallEtaleInclusion X').sheafPushforwardContinuous A
            (smallEtaleTopology X') (spacesEtaleTopology X'))).hom ≫
        whiskerLeft
            (Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) A
              (smallEtaleTopology Y) (spacesEtaleTopology X))
            (etaleRestrictionInclusionTwoSquare h A).natTrans ≫
          (associator
              (Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) A
                (smallEtaleTopology Y) (spacesEtaleTopology X))
              ((smallEtaleInclusion X).sheafPushforwardContinuous A
                (smallEtaleTopology X) (spacesEtaleTopology X))
              (etaleRestrictionSheaf h A)).inv).app G


end AlgebraicGeometry.AlgebraicSpace
