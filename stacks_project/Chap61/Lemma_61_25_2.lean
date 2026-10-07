module

import StacksCheckRecall
public import stacks_project.Chap61.Lemma_61_25_2_Comparison
public import stacks_project.Chap61.Lemma_61_25_2_Adjoint

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt
open scoped CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z] (i : Z ⟶ X) [IsClosedImmersion i]
variable [HasSheafify (affineIndEtaleTopology X) (Type (u + 1))]
variable [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
variable [HasSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
variable [HasSheafify (topology X) (Type (u + 1))]
variable [HasSheafify (topology Z) (Type (u + 1))]
variable [∀ P : (AffineIndEtale X)ᵒᵖ ⥤ Type (u + 1),
  (AffineIndEtale.baseChange i).op.HasLeftKanExtension P]
variable [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ Type (u + 1),
  (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F]
variable [∀ P : X.ProEtᵒᵖ ⥤ Type (u + 1),
  (smallProetalePullback i).op.HasLeftKanExtension P]
variable [Functor.HasPointwiseLeftKanExtension
  (AffineIndEtale.weaklyContractibleSheafifiedRepresentable Z)
  (AffineIndEtale.weaklyContractibleLiftSheafifiedRepresentable i)]
variable [Functor.HasPointwiseLeftKanExtension
  (AffineIndEtale.weaklyContractibleFreeAbelian Z)
  (AffineIndEtale.weaklyContractibleLiftFreeAbelian i)]

/- Lemma 61.25.2 (1): the morphism of topoi `i_proétale` of a closed immersion
of affine schemes equals the morphism of topoi associated to the fully faithful
cocontinuous functor `v`. -/
@[stacks 09BL] #check
  (AffineIndEtale.morphismOfTopoi_eq_ofContinuous i :
    (AffineIndEtale.baseChange i).sheafPullback (Type (u + 1))
        (affineIndEtaleTopology X) (affineIndEtaleTopology Z) ≅
      (AffineIndEtale.morphismOfTopoi i).inverseImage)

/- After restriction to affine ind-étale objects, inverse image along
`i_proétale` agrees with inverse image along `v`. -/
#check
  (AffineIndEtale.smallInverseImage_restrictionIso i :
    affineIndEtaleRestriction X ⋙
        (AffineIndEtale.morphismOfTopoi i).inverseImage ≅
      (smallProetalePullback i).sheafPullback (Type (u + 1))
          (topology X) (topology Z) ⋙
        affineIndEtaleRestriction Z)

/- Lemma 61.25.2 (2): inverse image of a type-valued sheaf is the sheaf
associated to the presheaf `V ↦ F(v(V))`. -/
@[stacks 09BL] #check
  (AffineIndEtale.inverseImage_sheafify i :
    ∀ F : Sheaf (affineIndEtaleTopology X) (Type (u + 1)),
      ((AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
            (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).obj F =
        (presheafToSheaf (affineIndEtaleTopology Z) (Type (u + 1))).obj
          ((AffineIndEtale.lift i).op ⋙ F.obj))

/- Lemma 61.25.2 (3): on a weakly contractible object `V` of `Z_app`,
`i⁻¹ F(V) = F(v(V))`. -/
@[stacks 09BL] #check
  (AffineIndEtale.inverseImage_obj_to_isIso i :
    ∀ (F : Sheaf (affineIndEtaleTopology X) (Type (u + 1)))
      (V : AffineIndEtale Z)
      [(affineIndEtaleTopology Z).IsWeaklyContractible V],
      IsIso (AffineIndEtale.inverseImage_obj_to i F V))

/- Lemma 61.25.2 (4): inverse image on sheaves of types has a left adjoint
`i^{Sh}_!`, obtained by extending `h_V ↦ h_{v(V)}` from weakly contractible
objects. -/
@[stacks 09BL] #check
  (AffineIndEtale.sheafLowerShriekAdjunction i :
    AffineIndEtale.sheafLowerShriek i ⊣
      (AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X))

/- Lemma 61.25.2 (5): inverse image on abelian sheaves has a left adjoint
`i_!`, obtained by extending `ℤ_V ↦ ℤ_{v(V)}` from weakly contractible
objects. -/
@[stacks 09BL] #check
  (AffineIndEtale.abelianLowerShriekAdjunction i :
    AffineIndEtale.abelianLowerShriek i ⊣
      AffineIndEtale.abelianInverseImage i)

/- Lemma 61.25.2 (6): the unit `id ⟶ i⁻¹ i^{Sh}_!` is an isomorphism. -/
@[stacks 09BL] #check
  (AffineIndEtale.sheafLowerShriek_unit_isIso i :
    IsIso (AffineIndEtale.sheafLowerShriekAdjunction i).unit)

/- Lemma 61.25.2 (7): the unit `id ⟶ i⁻¹ i_!` is an isomorphism. -/
@[stacks 09BL] #check
  (AffineIndEtale.abelianLowerShriek_unit_isIso i :
    IsIso (AffineIndEtale.abelianLowerShriekAdjunction i).unit)

/- Lemma 61.25.2 (8): the counit `i⁻¹ i_* ⟶ id` is an isomorphism. -/
@[stacks 09BL] #check
  (AffineIndEtale.inverseImage_pushforward_counit_isIso i :
    IsIso (AffineIndEtale.morphismOfTopoi i).adjunction.counit)

/- Lemma 61.25.2 (9): direct image `i_*` is fully faithful. -/
@[stacks 09BL] #check
  (AffineIndEtale.lift_sheafPushforwardCocontinuousFullyFaithful i :
    ((AffineIndEtale.lift i).sheafPushforwardCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).FullyFaithful)

/- Lemma 61.25.2 (10): type-valued lower shriek `i^{Sh}_!` is fully faithful. -/
@[stacks 09BL] #check
  (AffineIndEtale.sheafLowerShriekFullyFaithful i :
    (AffineIndEtale.sheafLowerShriek i).FullyFaithful)

/- Lemma 61.25.2 (11): abelian lower shriek `i_!` is fully faithful. -/
@[stacks 09BL] #check
  (AffineIndEtale.abelianLowerShriekFullyFaithful i :
    (AffineIndEtale.abelianLowerShriek i).FullyFaithful)
