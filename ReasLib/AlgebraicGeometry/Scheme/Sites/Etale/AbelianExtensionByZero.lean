/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}}

/-- Composition of the affine étale presentation with étale restriction is continuous. -/
instance affineRestriction_isContinuous (j : U ⟶ X) [Etale j] :
    Functor.IsContinuous (AffineEtale.Spec U ⋙ etaleRestriction j)
      (AffineEtale.topology U) X.smallEtaleTopology :=
  Functor.isContinuous_comp (AffineEtale.Spec U) (etaleRestriction j)
    (AffineEtale.topology U) U.smallEtaleTopology X.smallEtaleTopology

/-- The comma categories of affine étale restriction admit colimits of abelian groups. -/
instance affineRestriction_hasColimitsOfShape (j : U ⟶ X) [Etale j] (Y : X.Etaleᵒᵖ) :
    HasColimitsOfShape
      (CostructuredArrow (AffineEtale.Spec U ⋙ etaleRestriction j).op Y)
      AddCommGrpCat.{u} :=
  hasColimitsOfShape_of_essentiallySmall.{u} _ _

/-- The affine étale presentation supplies left Kan extensions along étale restriction. -/
instance affineRestriction_op_hasLeftKanExtension (j : U ⟶ X) [Etale j]
    (F : U.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (AffineEtale.Spec U ⋙ etaleRestriction j).op.HasLeftKanExtension F :=
  (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
    (AffineEtale.Spec U ⋙ etaleRestriction j).op F).hasLeftKanExtension

/-- Extension by zero of abelian étale sheaves, constructed through the affine étale site. -/
def abelianExtensionByZero (j : U ⟶ X) [Etale j] :
    Sheaf U.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (AffineEtale.sheafEquiv U AddCommGrpCat.{u}).inverse ⋙
    (AffineEtale.Spec U ⋙ etaleRestriction j).sheafPullback AddCommGrpCat.{u}
      (AffineEtale.topology U) X.smallEtaleTopology

/-- Restriction through the affine étale presentation is naturally isomorphic
to restriction on the small étale site. -/
def abelianRestrictionIso (j : U ⟶ X) [Etale j] :
    (AffineEtale.Spec U ⋙ etaleRestriction j).sheafPushforwardContinuous AddCommGrpCat.{u}
        (AffineEtale.topology U) X.smallEtaleTopology ⋙
      (AffineEtale.sheafEquiv U AddCommGrpCat.{u}).functor ≅
    etaleRestrictionSheaf j AddCommGrpCat.{u} :=
  Functor.isoWhiskerRight
      (Functor.sheafPushforwardContinuousComp (AffineEtale.Spec U) (etaleRestriction j)
        AddCommGrpCat.{u} (AffineEtale.topology U) U.smallEtaleTopology
        X.smallEtaleTopology).symm
      (AffineEtale.sheafEquiv U AddCommGrpCat.{u}).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (AffineEtale.sheafEquiv U AddCommGrpCat.{u}).counitIso ≪≫
    Functor.rightUnitor _

/-- Extension by zero of abelian étale sheaves is left adjoint to étale restriction. -/
def abelianExtensionByZeroAdjunction (j : U ⟶ X) [Etale j] :
    abelianExtensionByZero j ⊣ etaleRestrictionSheaf j AddCommGrpCat.{u} :=
  ((AffineEtale.sheafEquiv U AddCommGrpCat.{u}).symm.toAdjunction.comp
    (Functor.sheafAdjunctionContinuous (AffineEtale.Spec U ⋙ etaleRestriction j)
      AddCommGrpCat.{u} (AffineEtale.topology U) X.smallEtaleTopology)).ofNatIsoRight
    (abelianRestrictionIso j)

/-- The affine-site construction of abelian extension by zero agrees with the
full-site construction whenever the latter's Kan extensions and sheafification exist. -/
def abelianExtensionByZeroIso (j : U ⟶ X) [Etale j]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}] :
    abelianExtensionByZero j ≅ Scheme.abelianExtensionByZero j :=
  Adjunction.leftAdjointUniq (abelianExtensionByZeroAdjunction j)
    (Scheme.abelianExtensionByZero_adjunction j)

end AlgebraicGeometry.Scheme.Etale
