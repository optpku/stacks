/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import stacks_project.Chap66.Lemma_66_18_12_Comparison
public import stacks_project.Chap67.Definition_67_13_2_InverseImage

/-!
# Étale localization of cohomology with support

An étale morphism `f : X ⟶ Y` of algebraic spaces that is an isomorphism over a closed
subspace `Z ⊂ Y` identifies cohomology with support in `Z` with cohomology with support in
`f⁻¹(Z)`. Sheaves on `Z` and on `f⁻¹(Z)` are compared by restriction along `inverseImageTo`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Adjunction
open Opposite

noncomputable section

universe u v w

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived`
-- pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of
-- `RightDerived.postcompIso`/`precompIso`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- An isomorphism of algebraic spaces is étale. -/
instance instEtale_inverseImageTo_of_isIso {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIso (inverseImageTo f i)] :
    Etale (inverseImageTo f i) :=
  sorry

/-- Global sections with support along a closed immersion, as the composite of the
sections-with-support functor on `Z_étale` with `Sheaf.functorH` in degree zero. -/
def gammaWithSupport {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (sectionsWithSupport :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})] :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sectionsWithSupport ⋙ Sheaf.functorH (smallEtaleTopology Z) 0

/-- `gammaWithSupport` is sections with support followed by degree-zero sheaf cohomology on `Z`. -/
theorem gammaWithSupport_eq {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (sectionsWithSupport :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})] :
    gammaWithSupport i sectionsWithSupport =
      sectionsWithSupport ⋙ Sheaf.functorH (smallEtaleTopology Z) 0 :=
  rfl

/-- The inverse fibre-product comparison of a cartesian square with étale horizontals, as a
morphism of functors of points. -/
def etaleBaseChangeRestrictMapInvNat {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (V' : smallEtaleSite Y') :
    etaleBaseChangeFunctorOfPoints f ((etaleRestriction g).obj V') ⟶
      etaleBaseChangeFunctorOfPoints f' V' :=
  pullback.lift
    (h_cart.lift
      (etaleBaseChangeHom f ((etaleRestriction g).obj V'))
      (etaleBaseChangeSnd f ((etaleRestriction g).obj V') ≫ V'.hom) sorry)
    (etaleBaseChangeSndNat f ((etaleRestriction g).obj V')) sorry

/-- The inverse fibre-product comparison as a morphism of spaces étale over `X`. -/
def etaleBaseChangeRestrictMapInv {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (V' : smallEtaleSite Y') :
    (etaleBaseChange f).obj ((etaleRestriction g).obj V') ⟶
      (spacesEtaleRestriction h).obj ((etaleBaseChange f').obj V') :=
  MorphismProperty.Over.homMk (etaleBaseChangeRestrictMapInvNat h_cart V') sorry

/-- The inverse site-level natural transformation comparing fibre products along a cartesian
square with étale horizontals. -/
def etaleBaseChangeRestrictNatTransInv {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] :
    etaleRestriction g ⋙ etaleBaseChange f ⟶
      etaleBaseChange f' ⋙ spacesEtaleRestriction h where
  app := etaleBaseChangeRestrictMapInv h_cart
  naturality := sorry

/-- Continuous sheaf pushforward of the inverse fibre-product comparison. -/
def etaleBaseChangeRestrictSheafHomInv {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
    (A : Type v) [Category.{w} A] :
    (etaleBaseChange f' ⋙ spacesEtaleRestriction h).sheafPushforwardContinuous A
        (smallEtaleTopology Y') (spacesEtaleTopology X) ⟶
      (etaleRestriction g ⋙ etaleBaseChange f).sheafPushforwardContinuous A
        (smallEtaleTopology Y') (spacesEtaleTopology X) :=
  sheafPushforwardContinuousNatTrans (etaleBaseChangeRestrictNatTransInv h_cart) A
    (smallEtaleTopology Y') (spacesEtaleTopology X)

/-- The inverse of an étale isomorphism of algebraic spaces is étale. -/
instance instEtale_inv_of_isIso {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] : Etale (inv φ) :=
  sorry

/-- Restriction along an étale isomorphism and its inverse is isomorphic to the identity
on the small étale site of the source. -/
def etaleRestriction_comp_inv {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] :
    etaleRestriction φ ⋙ etaleRestriction (inv φ) ≅ 𝟭 (smallEtaleSite X) :=
  NatIso.ofComponents
    (fun U =>
      MorphismProperty.Comma.isoMk
        (X := (etaleRestriction φ ⋙ etaleRestriction (inv φ)).obj U) (Y := U)
        (Iso.refl U.left) (Iso.refl U.right) sorry)
    sorry

/-- Restriction along the inverse of an étale isomorphism, then along the isomorphism, is
isomorphic to the identity on the small étale site of the target. -/
def etaleRestriction_inv_comp {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] :
    etaleRestriction (inv φ) ⋙ etaleRestriction φ ≅ 𝟭 (smallEtaleSite Y) :=
  NatIso.ofComponents
    (fun U =>
      MorphismProperty.Comma.isoMk
        (X := (etaleRestriction (inv φ) ⋙ etaleRestriction φ).obj U) (Y := U)
        (Iso.refl U.left) (Iso.refl U.right) sorry)
    sorry

/-- Spaces étale restriction along an étale isomorphism and its inverse is isomorphic to the
identity. -/
def spacesEtaleRestriction_comp_inv {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] :
    spacesEtaleRestriction φ ⋙ spacesEtaleRestriction (inv φ) ≅ 𝟭 (spacesEtaleSite X) :=
  NatIso.ofComponents
    (fun U =>
      MorphismProperty.Over.isoMk
        (A := (spacesEtaleRestriction φ ⋙ spacesEtaleRestriction (inv φ)).obj U)
        (B := U) (Iso.refl U.left) sorry)
    sorry

/-- Spaces étale restriction along the inverse of an étale isomorphism, then along the
isomorphism, is isomorphic to the identity. -/
def spacesEtaleRestriction_inv_comp {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] :
    spacesEtaleRestriction (inv φ) ⋙ spacesEtaleRestriction φ ≅ 𝟭 (spacesEtaleSite Y) :=
  NatIso.ofComponents
    (fun U =>
      MorphismProperty.Over.isoMk
        (A := (spacesEtaleRestriction (inv φ) ⋙ spacesEtaleRestriction φ).obj U)
        (B := U) (Iso.refl U.left) sorry)
    sorry

instance etaleRestriction_comp_inv_isContinuous {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] :
    (etaleRestriction φ ⋙ etaleRestriction (inv φ)).IsContinuous
      (smallEtaleTopology X) (smallEtaleTopology X) :=
  Functor.isContinuous_comp (etaleRestriction φ) (etaleRestriction (inv φ))
    (smallEtaleTopology X) (smallEtaleTopology Y) (smallEtaleTopology X)

instance etaleRestriction_inv_comp_isContinuous {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] :
    (etaleRestriction (inv φ) ⋙ etaleRestriction φ).IsContinuous
      (smallEtaleTopology Y) (smallEtaleTopology Y) :=
  Functor.isContinuous_comp (etaleRestriction (inv φ)) (etaleRestriction φ)
    (smallEtaleTopology Y) (smallEtaleTopology X) (smallEtaleTopology Y)

instance spacesEtaleRestriction_comp_inv_isContinuous {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] :
    (spacesEtaleRestriction φ ⋙ spacesEtaleRestriction (inv φ)).IsContinuous
      (spacesEtaleTopology X) (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (spacesEtaleRestriction φ) (spacesEtaleRestriction (inv φ))
    (spacesEtaleTopology X) (spacesEtaleTopology Y) (spacesEtaleTopology X)

instance spacesEtaleRestriction_inv_comp_isContinuous {X Y : AlgebraicSpace S} (φ : X ⟶ Y)
    [IsIso φ] [Etale φ] :
    (spacesEtaleRestriction (inv φ) ⋙ spacesEtaleRestriction φ).IsContinuous
      (spacesEtaleTopology Y) (spacesEtaleTopology Y) :=
  Functor.isContinuous_comp (spacesEtaleRestriction (inv φ)) (spacesEtaleRestriction φ)
    (spacesEtaleTopology Y) (spacesEtaleTopology X) (spacesEtaleTopology Y)

instance id_smallEtale_isContinuous (X : AlgebraicSpace S) :
    (𝟭 (smallEtaleSite X)).IsContinuous (smallEtaleTopology X) (smallEtaleTopology X) :=
  inferInstance

instance id_spacesEtale_isContinuous (X : AlgebraicSpace S) :
    (𝟭 (spacesEtaleSite X)).IsContinuous (spacesEtaleTopology X) (spacesEtaleTopology X) :=
  inferInstance

/-- Inverse of `restrictionExtensionMate`, obtained by conjugating the mate of `inv φ`. -/
def restrictionExtensionMateInv {U V : AlgebraicSpace S} (φ : U ⟶ V) [IsIso φ] [Etale φ]
    (A : Type v) [Category.{w} A]
    [∀ P : (smallEtaleSite V)ᵒᵖ ⥤ A,
      (smallEtaleInclusion V).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallEtaleSite U)ᵒᵖ ⥤ A,
      (smallEtaleInclusion U).op.HasPointwiseRightKanExtension P] :
    (etaleRestriction φ).sheafPushforwardContinuous A
          (smallEtaleTopology U) (smallEtaleTopology V) ⋙
        (smallEtaleInclusion U).sheafPushforwardCocontinuous A
          (smallEtaleTopology U) (spacesEtaleTopology U) ⟶
      (smallEtaleInclusion V).sheafPushforwardCocontinuous A
          (smallEtaleTopology V) (spacesEtaleTopology V) ⋙
        (spacesEtaleRestriction φ).sheafPushforwardContinuous A
          (spacesEtaleTopology U) (spacesEtaleTopology V) :=
  let Fφ := (etaleRestriction φ).sheafPushforwardContinuous A
      (smallEtaleTopology U) (smallEtaleTopology V)
  let Fψ := (etaleRestriction (inv φ)).sheafPushforwardContinuous A
      (smallEtaleTopology V) (smallEtaleTopology U)
  let Sφ := (spacesEtaleRestriction φ).sheafPushforwardContinuous A
      (spacesEtaleTopology U) (spacesEtaleTopology V)
  let Sψ := (spacesEtaleRestriction (inv φ)).sheafPushforwardContinuous A
      (spacesEtaleTopology V) (spacesEtaleTopology U)
  let iU := (smallEtaleInclusion U).sheafPushforwardCocontinuous A
      (smallEtaleTopology U) (spacesEtaleTopology U)
  let iV := (smallEtaleInclusion V).sheafPushforwardCocontinuous A
      (smallEtaleTopology V) (spacesEtaleTopology V)
  (Functor.rightUnitor (Fφ ⋙ iU)).inv ≫
    whiskerLeft (Fφ ⋙ iU)
      (sheafPushforwardContinuousIso (spacesEtaleRestriction_comp_inv φ) A
        (spacesEtaleTopology U) (spacesEtaleTopology U)).inv ≫
    (Functor.associator Fφ iU (Sψ ⋙ Sφ)).hom ≫
    whiskerLeft Fφ (Functor.associator iU Sψ Sφ).inv ≫
    whiskerLeft Fφ (whiskerRight (restrictionExtensionMate (inv φ) A) Sφ) ≫
    whiskerLeft Fφ (Functor.associator Fψ iV Sφ).hom ≫
    (Functor.associator Fφ Fψ (iV ⋙ Sφ)).inv ≫
    whiskerRight
      (sheafPushforwardContinuousIso (etaleRestriction_inv_comp φ) A
        (smallEtaleTopology V) (smallEtaleTopology V)).hom
      (iV ⋙ Sφ) ≫
    (Functor.leftUnitor (iV ⋙ Sφ)).hom

variable {X' X Y' Y : AlgebraicSpace S}
variable {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The reverse Beck–Chevalley morphism
`h^* f'_small,* ⟶ f_small,* g^*` of a cartesian square with étale horizontals. -/
def pushforwardEtaleBaseChangeNatTransInv (h_cart : IsPullback h f' f g)
    [Etale g] [Etale h] [IsIso h]
    (A : Type v) [Category.{w} A]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallEtaleSite X')ᵒᵖ ⥤ A,
      (smallEtaleInclusion X').op.HasPointwiseRightKanExtension P] :
    etaleRestrictionSheaf h A ⋙ sheafPushforward A f' ⟶
      sheafPushforward A f ⋙ etaleRestrictionSheaf g A :=
  whiskerRight (restrictionExtensionMateInv h A)
      ((etaleBaseChange f').sheafPushforwardContinuous A
        (smallEtaleTopology Y') (spacesEtaleTopology X')) ≫
    whiskerLeft
      ((smallEtaleInclusion X).sheafPushforwardCocontinuous A
        (smallEtaleTopology X) (spacesEtaleTopology X))
      (etaleBaseChangeRestrictSheafHomInv h_cart A)

variable {X Y Z : AlgebraicSpace S} {f : X ⟶ Y} {i : Z ⟶ Y}
variable [Etale f] [IsClosedImmersion i] [IsIso (inverseImageTo f i)]

/-- The mate of the inverse étale Beck–Chevalley 2-cell of `i_*` along the support adjunctions. -/
def sectionsWithSupportEtaleBaseChangeNatTrans
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX) :
    sectionsWithSupportY ⋙
        etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1} ⟶
      etaleRestrictionSheaf f AddCommGrpCat.{u + 1} ⋙ sectionsWithSupportX :=
  (mateEquiv adjY adjX
    (TwoSquare.mk _ _ _ _
      (pushforwardEtaleBaseChangeNatTransInv
        ((inverseImage_isPullback f i).flip) AddCommGrpCat.{u + 1}))).natTrans

/-- The underived comparison
`ℋ_Z(F)|_{f⁻¹(Z)} ⟶ ℋ_{f⁻¹(Z)}(F|_X)` of abelian sheaves on `f⁻¹(Z)`. -/
def sectionsWithSupportEtaleBaseChangeHom
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).obj
        (sectionsWithSupportY.obj F) ⟶
      sectionsWithSupportX.obj ((etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj F) :=
  (sectionsWithSupportEtaleBaseChangeNatTrans
    sectionsWithSupportY adjY sectionsWithSupportX adjX).app F

/-- The underived comparison morphism is the component of the corresponding natural
transformation. -/
theorem sectionsWithSupportEtaleBaseChangeHom_app
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    sectionsWithSupportEtaleBaseChangeHom
        sectionsWithSupportY adjY sectionsWithSupportX adjX F =
      (sectionsWithSupportEtaleBaseChangeNatTrans
        sectionsWithSupportY adjY sectionsWithSupportX adjX).app F :=
  rfl

/-- The underived comparison of sections with support is an isomorphism. -/
theorem isIso_sectionsWithSupportEtaleBaseChangeHom
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    IsIso (sectionsWithSupportEtaleBaseChangeHom
      sectionsWithSupportY adjY sectionsWithSupportX adjX F) :=
  sorry

/-- The derived sheaf comparison
`R^q ℋ_Z(F)|_{f⁻¹(Z)} ⟶ R^q ℋ_{f⁻¹(Z)}(F|_X)` of abelian sheaves on `f⁻¹(Z)`. -/
def higherSectionsWithSupportEtaleBaseChangeHom
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [sectionsWithSupportY.Additive] [sectionsWithSupportX.Additive]
    [(etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).PreservesInjectiveObjects]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ) :
    (etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).obj
        ((sectionsWithSupportY.rightDerived q).obj F) ⟶
      (sectionsWithSupportX.rightDerived q).obj
        ((etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj F) :=
  (Functor.RightDerived.postcompIso sectionsWithSupportY
        (etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}) q).inv.app F ≫
    (NatTrans.rightDerived
        (sectionsWithSupportEtaleBaseChangeNatTrans
          sectionsWithSupportY adjY sectionsWithSupportX adjX) q).app F ≫
      (Functor.RightDerived.precompIso
          (etaleRestrictionSheaf f AddCommGrpCat.{u + 1}) sectionsWithSupportX q).hom.app F

/-- The derived sheaf comparison is the `rightDerived` composite of the underived mate. -/
theorem higherSectionsWithSupportEtaleBaseChangeHom_eq
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [sectionsWithSupportY.Additive] [sectionsWithSupportX.Additive]
    [(etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).PreservesInjectiveObjects]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ) :
    higherSectionsWithSupportEtaleBaseChangeHom
        sectionsWithSupportY adjY sectionsWithSupportX adjX F q =
      (Functor.RightDerived.postcompIso sectionsWithSupportY
            (etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}) q).inv.app F ≫
        (NatTrans.rightDerived
            (sectionsWithSupportEtaleBaseChangeNatTrans
              sectionsWithSupportY adjY sectionsWithSupportX adjX) q).app F ≫
          (Functor.RightDerived.precompIso
              (etaleRestrictionSheaf f AddCommGrpCat.{u + 1})
              sectionsWithSupportX q).hom.app F :=
  rfl

/-- The comparison of global sections with support after transporting sheaves on `Z` to
`f⁻¹(Z)` along `inverseImageTo`. -/
def gammaWithSupportEtaleBaseChangeNatTrans
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    [HasSheafify (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})] :
    sectionsWithSupportY ⋙
        etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1} ⋙
          Sheaf.functorH (smallEtaleTopology (inverseImage f i)) 0 ⟶
      etaleRestrictionSheaf f AddCommGrpCat.{u + 1} ⋙
        gammaWithSupport (inverseImageι f i) sectionsWithSupportX :=
  whiskerRight
    (sectionsWithSupportEtaleBaseChangeNatTrans
      sectionsWithSupportY adjY sectionsWithSupportX adjX)
    (Sheaf.functorH (smallEtaleTopology (inverseImage f i)) 0)

/-- The derived global comparison
`H^q_Z(Y, F) ⟶ H^q_{f⁻¹(Z)}(X, F|_X)` after identifying sheaves on `Z` with sheaves on
`f⁻¹(Z)` by restriction along `inverseImageTo`. -/
def cohomologyWithSupportEtaleBaseChangeHom
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [sectionsWithSupportY.Additive] [sectionsWithSupportX.Additive]
    [(etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).PreservesInjectiveObjects]
    [(Sheaf.functorH (smallEtaleTopology (inverseImage f i)) 0).Additive]
    [(gammaWithSupport (inverseImageι f i) sectionsWithSupportX).Additive]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((sectionsWithSupportY ⋙
          etaleRestrictionSheaf (inverseImageTo f i) AddCommGrpCat.{u + 1} ⋙
            Sheaf.functorH (smallEtaleTopology (inverseImage f i)) 0).rightDerived q).obj F ⟶
      ((gammaWithSupport (inverseImageι f i) sectionsWithSupportX).rightDerived q).obj
        ((etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj F) :=
  (NatTrans.rightDerived
        (gammaWithSupportEtaleBaseChangeNatTrans
          sectionsWithSupportY adjY sectionsWithSupportX adjX) q).app F ≫
    (Functor.RightDerived.precompIso (etaleRestrictionSheaf f AddCommGrpCat.{u + 1})
        (gammaWithSupport (inverseImageι f i) sectionsWithSupportX) q).hom.app F

end AlgebraicGeometry.AlgebraicSpace
