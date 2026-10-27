/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.LocalComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.PresentationComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # Structure modules and presentations of scheme restriction -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry (Scheme)

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

variable {S : Scheme.{u}}

/-- The ringed-site composite from the small étale site of `ofOver U` to the open-subscheme
ringed site of `U.left`. -/
noncomputable def restrictToOpensHom (U : Over S) :
    RingedSite.Hom (ringedSite (ofOver U))
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (U.left : TopCat))
        ⟨Scheme.Site.structurePresheaf (U.left.restrictFunctor ⋙ Over.forget U.left),
          opensStructurePresheaf_isSheaf U.left⟩) :=
  RingedSite.Hom.comp (schemeEtaleRingedHom U) (smallEtaleToOpensRingedHom U.left)

/-- Continuity of the named restriction functor, projected from its ringed-site morphism. -/
theorem restrictToOpensHom_isContinuous (U : Over S) :
    (restrictToOpensHom U).base.IsContinuous
      (Opens.grothendieckTopology (U.left : TopCat)) (smallEtaleTopology (ofOver U)) :=
  RingedSite.Hom.base_isContinuous (restrictToOpensHom U)

/-- Identification of the two-stage module pushforward in `restrictToScheme` with pushforward
along `restrictToOpensHom`. -/
noncomputable def restrictToOpensPushforwardIso (U : Over S) :
    (schemeEtaleRingedHom U).modulePushforward.{u} ⋙
        (smallEtaleToOpensRingedHom U.left).modulePushforward.{u} ≅
      (restrictToOpensHom U).modulePushforward.{u} :=
  RingedSite.Hom.modulePushforwardCompIso.{u}
    (schemeEtaleRingedHom U) (smallEtaleToOpensRingedHom U.left)

/-- Transport of `restrictToScheme` along the module-pushforward composite of
`restrictToOpensHom`. -/
noncomputable def restrictToSchemeOpensIso {U : Over S} (F : (ofOver U).Modules) :
    (Modules.restrictToScheme U).obj F ≅
      (opensToSchemeModules U.left).obj
        ((restrictToOpensHom U).modulePushforward.{u}.obj
          ((Modules.restrictFunctor (𝟙 (ofOver U))).obj F)) :=
  (Modules.RestrictToScheme.restrictionIsoBare U).app F ≪≫
    (Modules.RestrictToScheme.restrictionBare U).mapIso
      ((Modules.RestrictToScheme.identityRestrictionIso U).app F).symm ≪≫
    (opensToSchemeModules U.left).mapIso
      ((restrictToOpensPushforwardIso U).app ((Modules.restrictFunctor (𝟙 (ofOver U))).obj F))

/-! The two coefficient maps used by `unitMap` have explicit reverse transports.  The
first one is the inverse of the scheme restriction/global-sections comparison, while
the second one is the identity comparison for the presentation site. -/

private def openChartUnitInv (U : Over S) :
    (SmallEtale.Modules.toScheme (tautologicalChart U)).obj
        (SheafOfModules.unit (SmallEtale.structureSheaf (ofOver U))) ⟶
      SheafOfModules.unit U.left.ringCatSheaf where
  val :=
    { app := fun V ↦ by
        let A := ((SmallEtale.Modules.toScheme (tautologicalChart U)).obj
          (SheafOfModules.unit (SmallEtale.structureSheaf (ofOver U)))).val.obj V
        let B := (SheafOfModules.unit U.left.ringCatSheaf).val.obj V
        letI : AddCommGroup A := A.isAddCommGroup
        letI : Module (U.left.ringCatSheaf.obj.obj V) A := A.isModule
        letI : AddCommGroup B := B.isAddCommGroup
        letI : Module (U.left.ringCatSheaf.obj.obj V) B := B.isModule
        exact @ModuleCat.ofHom (U.left.ringCatSheaf.obj.obj V) _ A B
          A.isAddCommGroup A.isModule B.isAddCommGroup B.isModule
          { toFun := fun x ↦ ((Scheme.restrictFunctorΓ (X := U.left)).hom.app V).hom x
            map_add' := by sorry
            map_smul' := by sorry }
      naturality := by sorry }

private def toPresentationSchemeComparison {S : Scheme.{u}} (X : AlgebraicSpace S) :
    SmallEtale.toScheme X ⟶ SmallEtale.toPresentation X ⋙ smallEtaleToScheme X where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

private noncomputable def toPresentationStructureMapInv {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ((SmallEtale.toPresentation X).sheafPushforwardContinuous RingCat.{u}
      (SmallEtale.topology X) (smallEtaleTopology X)).obj (structureSheaf X) ⟶
      SmallEtale.structureSheaf X :=
  Scheme.Site.inverseStructureSheafMap
    (SmallEtale.topology X) (smallEtaleTopology X)
    (SmallEtale.toScheme X) (smallEtaleToScheme X)
    (SmallEtale.toPresentation X) (toPresentationSchemeComparison X)
    (SmallEtale.structurePresheaf_isSheaf X) (structurePresheaf_isSheaf X)

private def toPresentationUnitInv {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (SheafOfModules.pushforward (toPresentationStructureMap X)).obj
        (SheafOfModules.unit (structureSheaf X)) ⟶
      SheafOfModules.unit (SmallEtale.structureSheaf X) where
  val :=
    { app := fun V ↦ by
        let A := ((SheafOfModules.pushforward (toPresentationStructureMap X)).obj
          (SheafOfModules.unit (structureSheaf X))).val.obj V
        let B := (SheafOfModules.unit (SmallEtale.structureSheaf X)).val.obj V
        letI : AddCommGroup A := A.isAddCommGroup
        letI : Module ((SmallEtale.structureSheaf X).obj.obj V) A := A.isModule
        letI : AddCommGroup B := B.isAddCommGroup
        letI : Module ((SmallEtale.structureSheaf X).obj.obj V) B := B.isModule
        exact @ModuleCat.ofHom ((SmallEtale.structureSheaf X).obj.obj V) _ A B
          A.isAddCommGroup A.isModule B.isAddCommGroup B.isModule
          { toFun := fun x ↦ (toPresentationStructureMapInv X).hom.app V x
            map_add' := by sorry
            map_smul' := by sorry }
      naturality := by sorry }

private def unitMapInv (U : Over S) :
    (Modules.restrictToScheme U).obj
        (SheafOfModules.unit (structureSheaf (ofOver U))) ⟶
      SheafOfModules.unit U.left.ringCatSheaf :=
  (SmallEtale.Modules.toScheme (tautologicalChart U)).map
      (toPresentationUnitInv (ofOver U)) ≫ openChartUnitInv U

private noncomputable def unitMapIso (U : Over S) :
    SheafOfModules.unit U.left.ringCatSheaf ≅
      (Modules.restrictToScheme U).obj
        (SheafOfModules.unit (structureSheaf (ofOver U))) where
  hom := unitMap U
  inv := unitMapInv U
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- Restriction to the underlying scheme preserves zero module morphisms. -/
instance preservesZeroMorphisms (U : Over S) :
    (Modules.restrictToScheme U).PreservesZeroMorphisms := sorry

/-- The coefficient comparison identifies the scheme and restricted structure modules. -/
instance unitMap_isIso (U : Over S) : IsIso (unitMap U) :=
  (unitMapIso U).isIso_hom

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
