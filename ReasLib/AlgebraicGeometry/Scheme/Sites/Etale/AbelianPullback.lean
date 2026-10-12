/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {S T : Scheme.{u}}

/-- Base change on the affine étale presentation is continuous. -/
instance affineBaseChange_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (AffineEtale.Spec S ⋙ smallEtalePullback f)
      (AffineEtale.topology S) T.smallEtaleTopology :=
  Functor.isContinuous_comp (AffineEtale.Spec S) (smallEtalePullback f)
    (AffineEtale.topology S) S.smallEtaleTopology T.smallEtaleTopology

/-- The comma categories of affine étale base change admit colimits of abelian groups. -/
instance affineBaseChange_hasColimitsOfShape (f : T ⟶ S) (Y : T.Etaleᵒᵖ) :
    HasColimitsOfShape
      (CostructuredArrow (AffineEtale.Spec S ⋙ smallEtalePullback f).op Y)
      AddCommGrpCat.{u} :=
  hasColimitsOfShape_of_essentiallySmall.{u} _ _

/-- The affine presentation supplies the left Kan extensions used by sheaf pullback. -/
instance affineBaseChange_op_hasLeftKanExtension (f : T ⟶ S)
    (F : S.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (AffineEtale.Spec S ⋙ smallEtalePullback f).op.HasLeftKanExtension F :=
  (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
    (AffineEtale.Spec S ⋙ smallEtalePullback f).op F).hasLeftKanExtension

/-- Continuous pushforward along affine base change has the canonical left adjoint. -/
instance affineBaseChange_isRightAdjoint (f : T ⟶ S) :
    ((AffineEtale.Spec S ⋙ smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (AffineEtale.topology S) T.smallEtaleTopology).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (AffineEtale.Spec S ⋙ smallEtalePullback f) AddCommGrpCat.{u}
      (AffineEtale.topology S) T.smallEtaleTopology).isRightAdjoint

/-- The inverse-image functor on abelian sheaves induced by a scheme morphism. -/
noncomputable def abelianInverseImage (f : T ⟶ S) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u} :=
  (AffineEtale.sheafEquiv S AddCommGrpCat.{u}).inverse ⋙
    (AffineEtale.Spec S ⋙ smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
      (AffineEtale.topology S) T.smallEtaleTopology

/-- The inverse-image/direct-image adjunction for abelian étale sheaves. -/
def abelianAdjunction (f : T ⟶ S) :
    abelianInverseImage f ⊣
      (AffineEtale.Spec S ⋙ smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (AffineEtale.topology S) T.smallEtaleTopology ⋙
        (AffineEtale.sheafEquiv S AddCommGrpCat.{u}).functor := by
  dsimp [abelianInverseImage]
  exact (AffineEtale.sheafEquiv S AddCommGrpCat.{u}).symm.toAdjunction.comp
    (Functor.sheafAdjunctionContinuous (AffineEtale.Spec S ⋙ smallEtalePullback f)
      AddCommGrpCat.{u} (AffineEtale.topology S) T.smallEtaleTopology)

/-- The right adjoint obtained from the affine étale presentation is naturally
isomorphic to continuous direct image on the small étale site. -/
def abelianDirectImageIso (f : T ⟶ S) :
    (AffineEtale.Spec S ⋙ smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (AffineEtale.topology S) T.smallEtaleTopology ⋙
      (AffineEtale.sheafEquiv S AddCommGrpCat.{u}).functor ≅
    (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology :=
  Functor.isoWhiskerRight
      (Functor.sheafPushforwardContinuousComp (AffineEtale.Spec S) (smallEtalePullback f)
        AddCommGrpCat.{u} (AffineEtale.topology S) S.smallEtaleTopology
        T.smallEtaleTopology).symm
      (AffineEtale.sheafEquiv S AddCommGrpCat.{u}).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (AffineEtale.sheafEquiv S AddCommGrpCat.{u}).counitIso ≪≫
    Functor.rightUnitor _

/-- Inverse image of abelian étale sheaves is left adjoint to ordinary continuous
direct image on the small étale site. -/
def abelianAdjunctionDirectImage (f : T ⟶ S) :
    abelianInverseImage f ⊣
      (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology :=
  (abelianAdjunction f).ofNatIsoRight (abelianDirectImageIso f)

end AlgebraicGeometry.Scheme.Etale
