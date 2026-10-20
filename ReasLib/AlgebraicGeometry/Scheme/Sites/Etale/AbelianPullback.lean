/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
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

/-- Restriction of an abelian sheaf along a morphism of schemes on small étale sites. -/
noncomputable def etaleAbelianRestriction {X Z : Scheme.{u}} (i : Z ⟶ X)
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} :=
  (smallEtalePullback i).sheafPullback AddCommGrpCat.{u}
    X.smallEtaleTopology Z.smallEtaleTopology

/-- Evaluating restriction recovers sheaf pullback along `smallEtalePullback`. -/
theorem etaleAbelianRestriction_eq {X Z : Scheme.{u}} (i : Z ⟶ X)
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    etaleAbelianRestriction i =
      (smallEtalePullback i).sheafPullback AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology :=
  rfl

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme.Hom

/-- Continuous sheaf pushforward along a small-étale pullback is a right adjoint. -/
public instance instIsRightAdjoint_smallEtaleSheafPushforwardContinuous
    {Z Z' : Scheme.{u}} {p : Z' ⟶ Z} :
    ((smallEtalePullback p).sheafPushforwardContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology Z'.smallEtaleTopology).IsRightAdjoint :=
  (Etale.abelianAdjunctionDirectImage p).isRightAdjoint

/-- Sheaf pullback of abelian sheaves along a small-étale base change. -/
noncomputable abbrev etaleAbelianSheafPullback {Z Z' : Scheme.{u}} (p : Z' ⟶ Z) :
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u} :=
  (smallEtalePullback p).sheafPullback AddCommGrpCat.{u}
    Z.smallEtaleTopology Z'.smallEtaleTopology

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Etale

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

/-- Site-level adjunction `etaleRestriction ⊣ smallEtalePullback` along an
open immersion. -/
def etaleOpenImmersionSiteAdj {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    etaleRestriction j ⊣ smallEtalePullback j :=
  MorphismProperty.Over.mapPullbackAdj (@Etale) ⊤ j inferInstance trivial

/-- The open-immersion site adjunction is `Over.mapPullbackAdj` for étale
morphisms. -/
theorem etaleOpenImmersionSiteAdj_eq {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    etaleOpenImmersionSiteAdj j =
      MorphismProperty.Over.mapPullbackAdj (@Etale) ⊤ j inferInstance trivial :=
  sorry

/-- Restriction of abelian étale sheaves along an open immersion agrees with
small-étale inverse image. -/
def etaleRestrictionSheafIsoPullback {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    etaleRestrictionSheaf j AddCommGrpCat.{u} ≅ etaleAbelianSheafPullback j :=
  ((Adjunction.sheafPushforwardContinuous (etaleOpenImmersionSiteAdj j)
        U.smallEtaleTopology X.smallEtaleTopology :
      etaleRestrictionSheaf j AddCommGrpCat.{u} ⊣
        (smallEtalePullback j).sheafPushforwardContinuous AddCommGrpCat.{u}
          X.smallEtaleTopology U.smallEtaleTopology).leftAdjointUniq
    ((smallEtalePullback j).sheafAdjunctionContinuous AddCommGrpCat.{u}
      X.smallEtaleTopology U.smallEtaleTopology))

/-- The open-immersion restriction/pullback comparison at an abelian étale
sheaf. -/
def etaleRestrictionSheafIsoPullback_app {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F ≅
      (etaleAbelianSheafPullback j).obj F :=
  (etaleRestrictionSheafIsoPullback j).app F

/-- The objectwise comparison is the component of
`etaleRestrictionSheafIsoPullback`. -/
theorem etaleRestrictionSheafIsoPullback_app_eq {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleRestrictionSheafIsoPullback_app j F =
      (etaleRestrictionSheafIsoPullback j).app F :=
  sorry

end AlgebraicGeometry.Scheme.Etale
