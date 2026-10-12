/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianPullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}}

/-- Small-étale pushforward of abelian sheaves along a morphism of schemes. -/
noncomputable abbrev smallEtalePushforwardAb (f : X ⟶ Y) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  (Scheme.smallEtalePullback f).sheafPushforwardContinuous
    AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology

/-- The comma categories of affine étale base change have colimits of sets. -/
instance affineBaseChangeType_hasColimitsOfShape (f : X ⟶ Y) (U : X.Etaleᵒᵖ) :
    HasColimitsOfShape
      (CostructuredArrow (AffineEtale.Spec Y ⋙ Scheme.smallEtalePullback f).op U)
      (Type u) :=
  hasColimitsOfShape_of_essentiallySmall.{u} _ _

/-- Affine étale base change has left Kan extensions of set-valued presheaves. -/
instance affineBaseChangeType_op_hasLeftKanExtension (f : X ⟶ Y)
    (F : Y.AffineEtaleᵒᵖ ⥤ Type u) :
    (AffineEtale.Spec Y ⋙ Scheme.smallEtalePullback f).op.HasLeftKanExtension F :=
  (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
    (AffineEtale.Spec Y ⋙ Scheme.smallEtalePullback f).op F).hasLeftKanExtension

/-- Small-étale direct image of sheaves of sets has a left adjoint. -/
instance smallEtaleDirectImage_isRightAdjoint (f : X ⟶ Y) :
    ((Scheme.smallEtalePullback f).sheafPushforwardContinuous
      (Type u) Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint :=
  (Functor.isRightAdjoint_comp_iff_left (Scheme.smallEtaleDirectImage.{u,u} f)
    ((AffineEtale.Spec Y).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology Y) Y.smallEtaleTopology)).mp
    (Functor.isRightAdjoint_of_iso
      (Functor.sheafPushforwardContinuousComp (AffineEtale.Spec Y)
        (Scheme.smallEtalePullback f) (Type u) (AffineEtale.topology Y)
        Y.smallEtaleTopology X.smallEtaleTopology).symm)

/-- Small-étale direct image of abelian sheaves has a left adjoint. -/
instance smallEtalePushforwardAb_isRightAdjoint (f : X ⟶ Y) :
    (smallEtalePushforwardAb f).IsRightAdjoint :=
  (abelianAdjunctionDirectImage f).isRightAdjoint

end AlgebraicGeometry.Scheme.Etale
