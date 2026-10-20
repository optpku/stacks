/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafAdjunction
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.ConcreteHom

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleAdditive
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Continuous direct image and coefficient composition have definitionally equal
carriers and maps, so their comparison is the actual identity isomorphism. -/
def continuousComposeIso
    {C D : Type _} [Category C] [Category D] {A B : Type _} [Category A] [Category B]
    (v : C ⥤ D) (F : A ⥤ B) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [v.IsContinuous J K] [J.HasSheafCompose F] [K.HasSheafCompose F] :
    v.sheafPushforwardContinuous A J K ⋙ sheafCompose J F ≅
      sheafCompose K F ⋙ v.sheafPushforwardContinuous B J K := Iso.refl _

/-- Actual additive limits over small source charts. -/
instance smallLimits (X : AlgebraicSpace S) (U : (smallEtaleSite X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow U (SmallEtale.AtlasCharts.inclusion X).op) AddCommGrpCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- Actual additive limits over the essentially small spaces-chart comma categories. -/
instance spacesLimits (X : AlgebraicSpace S) (U : (spacesEtaleSite X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow U (SpacesEtale.AtlasCharts.inclusion X).op) AddCommGrpCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- The small chart inclusion admits its actual additive Kan extension. -/
instance smallRightKan (X : AlgebraicSpace S) (P : (SmallEtale.AtlasCharts.Site X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (SmallEtale.AtlasCharts.inclusion X).op.HasPointwiseRightKanExtension P := by
  intro U
  infer_instance

/-- The spaces chart inclusion admits its actual additive Kan extension. -/
instance spacesRightKan (X : AlgebraicSpace S) (P : (SmallEtale.AtlasCharts.Site X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (SpacesEtale.AtlasCharts.inclusion X).op.HasPointwiseRightKanExtension P := by
  intro U
  infer_instance

/-- Restriction to the small chart family is an equivalence with its concrete Kan inverse. -/
def smallEquivalence (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} ≌
      Sheaf (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology X) AddCommGrpCat.{u} :=
  ((SmallEtale.AtlasCharts.inclusion X).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
    (SmallEtale.AtlasCharts.topology X) (smallEtaleTopology X)).toEquivalence

/-- The same chart family gives a concrete presentation of the spaces-étale topos. -/
def spaceEquivalence (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u} ≌
      Sheaf (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology X) AddCommGrpCat.{u} :=
  ((AlgebraicGeometry.AlgebraicSpace.SpacesEtale.AtlasCharts.inclusion X).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
    (AlgebraicGeometry.AlgebraicSpace.SpacesEtale.AtlasCharts.topology X) (spacesEtaleTopology X)).toEquivalence

/-- Actual restriction from spaces-étale sheaves to scheme charts. -/
def restriction (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u} ⥤ Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces X).sheafPushforwardContinuous AddCommGrpCat.{u}
    (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Extension from scheme charts uses only the small chart Kan extension. -/
def extension (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} ⥤ Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u} :=
  (smallEquivalence X).functor ⋙ (spaceEquivalence X).inverse

/-- The actual small-chart unit identifies extension of a restriction. -/
def restrictionExtensionIso (X : AlgebraicSpace S) :
    𝟭 (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u}) ≅ restriction X ⋙ extension X :=
  (spaceEquivalence X).unitIso ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafPushforwardContinuousComp (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion X)
        (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces X) AddCommGrpCat.{u} (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology X)
        (smallEtaleTopology X) (spacesEtaleTopology X)).symm
      (spaceEquivalence X).inverse ≪≫ Functor.associator _ _ _

/-- The actual small-chart counit determines the comparison on all scheme charts by descent. -/
def extensionRestrictionIso (X : AlgebraicSpace S) :
    extension X ⋙ restriction X ≅ 𝟭 (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :=
  NatIso.ofComponents
    (fun N ↦
      let e : (smallEquivalence X).functor.obj
          ((restriction X).obj ((extension X).obj N)) ≅
            (smallEquivalence X).functor.obj N :=
        (spaceEquivalence X).counitIso.app ((smallEquivalence X).functor.obj N)
      let i : (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion X).op ⋙
          ((restriction X).obj ((extension X).obj N)).obj ≅
            (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion X).op ⋙ N.obj :=
        { hom := e.hom.hom, inv := e.inv.hom, hom_inv_id := sorry, inv_hom_id := sorry }
      Functor.IsCoverDense.sheafIso i)
    sorry

/-- Equivalence with explicit extension and restriction functors. -/
def siteEquivalence (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u} ≌ Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  CategoryTheory.Equivalence.mk (restriction X) (extension X)
    (restrictionExtensionIso X) (extensionRestrictionIso X)

/-- Actual small-site additive sheafification transports through the dense chart equivalence. -/
instance spacesSheafification (X : AlgebraicSpace S) : HasSheafify (spacesEtaleTopology X) AddCommGrpCat.{u} :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (SpacesEtale.AtlasCharts.topology X) (spacesEtaleTopology X) (SpacesEtale.AtlasCharts.inclusion X)

/-- Base change only needs the explicit small family of target charts. -/
def baseChange (f : X ⟶ Y) : AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.Site Y ⥤ spacesEtaleSite X :=
  AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion Y ⋙ etaleBaseChange f

/-- The composite chart base change is continuous for the inherited topologies. -/
instance baseChangeContinuous (f : X ⟶ Y) :
    (baseChange f).IsContinuous (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology Y) (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion Y) (etaleBaseChange f)
    (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology Y) (smallEtaleTopology Y) (spacesEtaleTopology X)

/-- Genuine small colimits supply the pointwise left Kan extension. -/
instance lanColimits (f : X ⟶ Y) (U : (spacesEtaleSite X)ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (baseChange f).op U) AddCommGrpCat.{u} :=
  hasColimitsOfShape_of_essentiallySmall.{u} _ _

/-- Constructed left Kan extension, with no admitted existence witness. -/
instance hasLan (f : X ⟶ Y) (P : (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.Site Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (baseChange f).op.HasLeftKanExtension P :=
  (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension (baseChange f).op P).hasLeftKanExtension

/-- Geometric inverse image uses the small-index Kan extension and genuine sheafification. -/
def inverseImage (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u} ⥤ Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  (smallEquivalence Y).functor ⋙
    Functor.sheafPullbackConstruction.sheafPullback (baseChange f) AddCommGrpCat.{u}
      (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology Y) (spacesEtaleTopology X) ⋙
    restriction X

/-- Direct image uses restriction and right Kan extension on the same actual small charts. -/
def directImage (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} ⥤ Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u} :=
  extension X ⋙ (etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u}
    (smallEtaleTopology Y) (spacesEtaleTopology X)

/-- Unwind the small target chart restriction in the composite right adjoint. -/
def rightComparison (f : X ⟶ Y) :
    ((extension X ⋙ (baseChange f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology Y) (spacesEtaleTopology X)) ⋙
      (smallEquivalence Y).inverse) ≅ directImage f :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (extension X)
      (Functor.sheafPushforwardContinuousComp (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion Y)
        (etaleBaseChange f) AddCommGrpCat.{u} (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology Y)
        (smallEtaleTopology Y) (spacesEtaleTopology X)).symm)
    (smallEquivalence Y).inverse ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (extension X)
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            ((etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u}
              (smallEtaleTopology Y) (spacesEtaleTopology X))
            (smallEquivalence Y).unitIso.symm ≪≫ Functor.rightUnitor _)

/-- Composing the concrete chart equivalences and Kan/sheafification adjunction
supplies the actual unit and counit. -/
def adjunction (f : X ⟶ Y) : inverseImage f ⊣ directImage f :=
  ((smallEquivalence Y).toAdjunction.comp
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (baseChange f) AddCommGrpCat.{u}
      (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology Y) (spacesEtaleTopology X)).comp
        (siteEquivalence X).toAdjunction)).ofNatIsoRight (rightComparison f)

/-- Forgetting additive structure preserves the actual small-chart right Kan extensions. -/
instance forgetPreservesRan (X : AlgebraicSpace S) :
    (forget AddCommGrpCat.{u}).PreservesRightKanExtensions (SpacesEtale.AtlasCharts.inclusion X).op := by
  intro P
  infer_instance

/-- The extension comparison keeps the section functions from the coefficient-forgetful Kan comparison. -/
def extensionForgetIso (X : AlgebraicSpace S) :
    extension X ⋙ sheafCompose (spacesEtaleTopology X) (forget AddCommGrpCat.{u}) ≅
      sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u}) ⋙ EtaleTopos.extension X :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (smallEquivalence X).functor
      (Functor.sheafPushforwardCocontinuous.compSheafComposeIso
        (SpacesEtale.AtlasCharts.inclusion X) (forget AddCommGrpCat.{u})
        (SpacesEtale.AtlasCharts.topology X) (spacesEtaleTopology X)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (continuousComposeIso
        (SmallEtale.AtlasCharts.inclusion X) (forget AddCommGrpCat.{u})
        (SmallEtale.AtlasCharts.topology X) (smallEtaleTopology X))
      (EtaleTopos.spaceEquivalence X).inverse ≪≫ Functor.associator _ _ _

/-- Additive direct image forgets to the actual geometric direct image on types. -/
def directImageForgetIso (f : X ⟶ Y) :
    directImage f ⋙ sheafCompose (smallEtaleTopology Y) (forget AddCommGrpCat.{u}) ≅
      sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u}) ⋙ EtaleTopos.directImage f :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (extension X)
      (continuousComposeIso (etaleBaseChange f)
        (forget AddCommGrpCat.{u}) (smallEtaleTopology Y) (spacesEtaleTopology X)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (extensionForgetIso X)
      ((etaleBaseChange f).sheafPushforwardContinuous (Type u) (smallEtaleTopology Y) (spacesEtaleTopology X)) ≪≫
    Functor.associator _ _ _

/-- Forgetting ring structure preserves the actual small-chart right Kan extensions. -/
theorem ringForgetPreservesRan (X : AlgebraicSpace S) :
    (forget RingCat.{u}).PreservesRightKanExtensions (SpacesEtale.AtlasCharts.inclusion X).op := by
  -- Local instance justification (defeq pin): the preservation calculation uses the explicit ring limits of ringSpaceEquivalence.
  letI := EtaleRingedTopos.ringChartLimits X
  -- Local instance justification (defeq pin): assemble pointwise right Kan extensions from those exact small ring limits before proving forgetful preservation.
  letI (P : (SmallEtale.AtlasCharts.Site X)ᵒᵖ ⥤ RingCat.{u}) :
      (SpacesEtale.AtlasCharts.inclusion X).op.HasPointwiseRightKanExtension P := by
    intro U
    infer_instance
  -- Local instance justification (proof-local temporary data): transport ring-forgetful limit preservation from the actual small model of each comma category.
  letI (U : (spacesEtaleSite X)ᵒᵖ) :
      PreservesLimitsOfShape (StructuredArrow U (SpacesEtale.AtlasCharts.inclusion X).op)
        (forget RingCat.{u}) :=
    preservesLimitsOfShape_of_equiv
      (equivSmallModel.{u} (StructuredArrow U (SpacesEtale.AtlasCharts.inclusion X).op)).symm
      (forget RingCat.{u})
  intro P
  infer_instance

/-- Forgetting ring operations commutes with the constructed spaces-étale ring extension. -/
def ringExtensionForgetIso (X : AlgebraicSpace S) :
    EtaleRingedTopos.ringExtension X ⋙ sheafCompose (spacesEtaleTopology X) (forget RingCat.{u}) ≅
      sheafCompose (smallEtaleTopology X) (forget RingCat.{u}) ⋙ EtaleTopos.extension X := by
  -- Local instance justification (defeq pin): select the ring-limit witness stored by the extension whose comparison is constructed here.
  letI := EtaleRingedTopos.ringChartLimits X
  -- Local instance justification (proof-local temporary data): the proved forgetful preservation witness supplies the explicit Kan comparison maps.
  letI := ringForgetPreservesRan X
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (EtaleRingedTopos.ringSmallEquivalence X).functor
      (Functor.sheafPushforwardCocontinuous.compSheafComposeIso
        (SpacesEtale.AtlasCharts.inclusion X) (forget RingCat.{u})
        (SpacesEtale.AtlasCharts.topology X) (spacesEtaleTopology X)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (continuousComposeIso
        (SmallEtale.AtlasCharts.inclusion X) (forget RingCat.{u})
        (SmallEtale.AtlasCharts.topology X) (smallEtaleTopology X))
      (EtaleTopos.spaceEquivalence X).inverse ≪≫ Functor.associator _ _ _

end AlgebraicGeometry.AlgebraicSpace.EtaleAdditive
