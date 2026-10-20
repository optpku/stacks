module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Isomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.EtaleBaseChange

/-! # Inverse étale base-change comparisons

Cartesian squares have concrete inverse fibre-product comparisons, yielding reverse
Beck–Chevalley morphisms when restriction on the source is along an isomorphism.
-/

-- Local declaration justification (metaprogramming implementation): exposed concrete maps
-- use private Prop-valued compatibility and naturality laws.
set_option backward.privateInPublic true

@[expose] public section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Functor
open Opposite
noncomputable section
universe u v w
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- The projections of the base-changed chart satisfy the cartesian compatibility. -/
private lemma etaleBaseChangeRestrictMapInvNat_inner_w {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (V' : smallEtaleSite Y') :
    etaleBaseChangeHom f ((etaleRestriction g).obj V') ≫ f =
      (etaleBaseChangeSnd f ((etaleRestriction g).obj V') ≫ V'.hom) ≫ g :=
  sorry

/-- The lifted chart and its second projection agree over the base. -/
private lemma etaleBaseChangeRestrictMapInvNat_outer_w {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (V' : smallEtaleSite Y') :
    homFunctor (h_cart.lift
      (etaleBaseChangeHom f ((etaleRestriction g).obj V'))
      (etaleBaseChangeSnd f ((etaleRestriction g).obj V') ≫ V'.hom)
      (etaleBaseChangeRestrictMapInvNat_inner_w h_cart V')) ≫ homFunctor f' =
      etaleBaseChangeSndNat f ((etaleRestriction g).obj V') ≫ homFunctor V'.hom :=
  sorry

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
      (etaleBaseChangeSnd f ((etaleRestriction g).obj V') ≫ V'.hom)
      (etaleBaseChangeRestrictMapInvNat_inner_w h_cart V'))
    (etaleBaseChangeSndNat f ((etaleRestriction g).obj V'))
    (etaleBaseChangeRestrictMapInvNat_outer_w h_cart V')

/-- The inverse fibre-product map respects the structure map to the source space. -/
private lemma etaleBaseChangeRestrictMapInv_w {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (V' : smallEtaleSite Y') :
    etaleBaseChangeRestrictMapInvNat h_cart V' ≫
        homFunctor ((spacesEtaleRestriction h).obj ((etaleBaseChange f').obj V')).hom =
      homFunctor ((etaleBaseChange f).obj ((etaleRestriction g).obj V')).hom :=
  sorry

/-- The inverse fibre-product comparison as a morphism of spaces étale over `X`. -/
def etaleBaseChangeRestrictMapInv {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (V' : smallEtaleSite Y') :
    (etaleBaseChange f).obj ((etaleRestriction g).obj V') ⟶
      (spacesEtaleRestriction h).obj ((etaleBaseChange f').obj V') :=
  MorphismProperty.Over.homMk (etaleBaseChangeRestrictMapInvNat h_cart V')
    (etaleBaseChangeRestrictMapInv_w h_cart V')

/-- Inverse fibre-product maps commute with morphisms of target charts. -/
private lemma etaleBaseChangeRestrictNatTransInv_naturality {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
    {U V : smallEtaleSite Y'} (k : U ⟶ V) :
    (etaleRestriction g ⋙ etaleBaseChange f).map k ≫
        etaleBaseChangeRestrictMapInv h_cart V =
      etaleBaseChangeRestrictMapInv h_cart U ≫
        (etaleBaseChange f' ⋙ spacesEtaleRestriction h).map k :=
  sorry

/-- The inverse site-level natural transformation comparing fibre products along a cartesian
square with étale horizontals. -/
def etaleBaseChangeRestrictNatTransInv {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] :
    etaleRestriction g ⋙ etaleBaseChange f ⟶
      etaleBaseChange f' ⋙ spacesEtaleRestriction h where
  app := etaleBaseChangeRestrictMapInv h_cart
  naturality := fun _ _ k => etaleBaseChangeRestrictNatTransInv_naturality h_cart k

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

/-- Inverse of `restrictionExtensionMate`, obtained by conjugating the mate of `inv φ`. -/
def restrictionExtensionMateInv {U V : AlgebraicSpace S} (φ : U ⟶ V) [IsIso φ] [Etale φ]
    (A : Type v) [Category.{w} A]
    [∀ P : (smallEtaleSite V)ᵒᵖ ⥤ A,
      (smallEtaleToSpaces V).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallEtaleSite U)ᵒᵖ ⥤ A,
      (smallEtaleToSpaces U).op.HasPointwiseRightKanExtension P] :
    (etaleRestriction φ).sheafPushforwardContinuous A
          (smallEtaleTopology U) (smallEtaleTopology V) ⋙
        (smallEtaleToSpaces U).sheafPushforwardCocontinuous A
          (smallEtaleTopology U) (spacesEtaleTopology U) ⟶
      (smallEtaleToSpaces V).sheafPushforwardCocontinuous A
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
  let iU := (smallEtaleToSpaces U).sheafPushforwardCocontinuous A
      (smallEtaleTopology U) (spacesEtaleTopology U)
  let iV := (smallEtaleToSpaces V).sheafPushforwardCocontinuous A
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
      (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallEtaleSite X')ᵒᵖ ⥤ A,
      (smallEtaleToSpaces X').op.HasPointwiseRightKanExtension P] :
    etaleRestrictionSheaf h A ⋙ sheafPushforward A f' ⟶
      sheafPushforward A f ⋙ etaleRestrictionSheaf g A :=
  whiskerRight (restrictionExtensionMateInv h A)
      ((etaleBaseChange f').sheafPushforwardContinuous A
        (smallEtaleTopology Y') (spacesEtaleTopology X')) ≫
    whiskerLeft
      ((smallEtaleToSpaces X).sheafPushforwardCocontinuous A
        (smallEtaleTopology X) (spacesEtaleTopology X))
      (etaleBaseChangeRestrictSheafHomInv h_cart A)


end AlgebraicGeometry.AlgebraicSpace
