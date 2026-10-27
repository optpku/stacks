/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.BigRelocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.InverseImage.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Module comparisons between big and small étale sites

Canonical coefficient restriction identifies the big étale structure sheaf on small charts.
Module pullback on the small site is constructed from geometric direct image and compared
with big-site pullback followed by relocalization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open RingedSite.Hom RingedSite.Cocontinuous

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

variable {S : Scheme.{u}}

/-- The coefficient map for the dense inclusion of small étale charts. -/
def smallChartStructureMap (X : AlgebraicSpace S) :
    structureSheaf X ⟶
      ((smallEtaleToSpaces X).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology X) (spacesEtaleTopology X)).obj (spacesStructureSheaf X) :=
  (EtaleRingedTopos.ringExtensionRestrictionIso X).inv.app (structureSheaf X)

/-- The small-chart coefficient map to the restriction of the big étale structure sheaf,
obtained by restricting the spaces-étale coefficient comparison. -/
def smallToBigStructureSheafMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheaf Y ⟶
      ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology Y) (overEtaleTopology X)).obj (Big.structureSheaf X) :=
  smallChartStructureMap Y ≫
    ((smallEtaleToSpaces Y).sheafPushforwardContinuous RingCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology Y)).map
        (SpacesToBig.relocalizationStructureSheafMap f) ≫
    (Functor.sheafPushforwardContinuousComp (smallEtaleToSpaces Y)
      (SpacesToBig.relocalizationFunctor f) RingCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology Y) (overEtaleTopology X)).hom.app
        (Big.structureSheaf X)

/-- On a small chart, the coefficient map first extends sections to the spaces-étale
structure sheaf and then applies its canonical comparison with global sections. -/
theorem smallToBigStructureSheafMap_app {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    (smallToBigStructureSheafMap f).hom.app U =
      (smallChartStructureMap Y).hom.app U ≫
        (SpacesToBig.relocalizationStructureSheafMap f).hom.app
          ((smallEtaleToSpaces Y).op.obj U) := rfl

/-- The canonical coefficient comparison on small charts is invertible. -/
instance smallToBigStructureSheafMap_isIso {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    IsIso (smallToBigStructureSheafMap f) := by
  exact Iso.isIso_hom
    (((EtaleRingedTopos.ringExtensionRestrictionIso Y).app (structureSheaf Y)).symm ≪≫
      ((smallEtaleToSpaces Y).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology Y) (spacesEtaleTopology Y)).mapIso
          (@asIso _ _ _ _ (SpacesToBig.relocalizationStructureSheafMap f)
            (SpacesToBig.relocalizationStructureSheafMap_isIso f)) ≪≫
      (Functor.sheafPushforwardContinuousComp (smallEtaleToSpaces Y)
        (SpacesToBig.relocalizationFunctor f) RingCat.{u}
        (smallEtaleTopology Y) (spacesEtaleTopology Y) (overEtaleTopology X)).app
          (Big.structureSheaf X))

/-- Underlying module inverse image `i_f^*` with coefficients `𝒪_Y`, via `i_f^♯`. -/
noncomputable def relocalizationModuleFunctor {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    RingedSite.ModuleCat.{u + 1} (Big.ringedSite X) ⥤
      RingedSite.ModuleCat.{u + 1} (ringedSite Y) :=
  moduleInverseImage (relocalizationFunctor f) (Big.structureSheaf X) ⋙
    SheafOfModules.restrictScalars.{u + 1} (smallToBigStructureSheafMap f)

/-- `relocalizationModuleFunctor f` preserves finite limits. -/
instance relocalizationModuleFunctor_preservesFiniteLimits {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    PreservesFiniteLimits (relocalizationModuleFunctor f) :=
  sorry

/-- `relocalizationModuleFunctor f` preserves finite colimits. -/
instance relocalizationModuleFunctor_preservesFiniteColimits {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    PreservesFiniteColimits (relocalizationModuleFunctor f) :=
  sorry

/-- Derived inverse image `i_f^* : D((Spaces/X)_étale, 𝒪) ⥤ D(Y_étale, 𝒪_Y)`. -/
noncomputable def relocalizationModuleDerived {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}] :
    ModuleDerived.{u + 1} (Big.ringedSite X) ⥤
      ModuleDerived.{u + 1} (ringedSite Y) :=
  @ExactFunctor.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (Big.ringedSite X)) _ _
    (moduleCat_hasDerivedCategory (Big.ringedSite X))
    (RingedSite.ModuleCat.{u + 1} (ringedSite Y)) _ _
    (moduleCat_hasDerivedCategory (ringedSite Y))
    (ExactFunctor.of (relocalizationModuleFunctor f))

/-- Module direct image of π_X is restriction to the small étale charts. -/
abbrev etalePiModulePushforward (X : AlgebraicSpace S) :=
  SheafOfModules.pushforward.{u + 1} (smallToBigStructureSheafMap (𝟙 X))

/-- Module pullback of π_X, as the left adjoint to its actual restriction functor. -/
abbrev etalePiModulePullback (X : AlgebraicSpace S)
    [(etalePiModulePushforward X).IsRightAdjoint] :=
  SheafOfModules.pullback.{u + 1} (smallToBigStructureSheafMap (𝟙 X))

/-- Independently defined small-site module direct image: extend to spaces-étale charts,
then evaluate on the geometric base change of each target chart. -/
def etaleSmallModulePushforward {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [(SheafOfModules.pushforward.{u + 1} (smallChartStructureMap Y)).IsRightAdjoint] :
    RingedSite.ModuleCat.{u + 1} (ringedSite Y) ⥤
      RingedSite.ModuleCat.{u + 1} (ringedSite X) :=
  SheafOfModules.pullback.{u + 1} (smallChartStructureMap Y) ⋙
    (spacesRingedHom f).modulePushforward.{u + 1} ⋙
      SheafOfModules.pushforward.{u + 1} (smallChartStructureMap X)

/-- The small-site module pullback is the left adjoint to the independent small direct image. -/
abbrev etaleSmallModulePullback {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [(SheafOfModules.pushforward.{u + 1} (smallChartStructureMap Y)).IsRightAdjoint]
    [(etaleSmallModulePushforward f).IsRightAdjoint] :=
  (etaleSmallModulePushforward f).leftAdjoint

/-- Module pullback is additive. -/
instance etalePiModulePullback_additive (X : AlgebraicSpace S)
    [(etalePiModulePushforward X).IsRightAdjoint] :
    (etalePiModulePullback X).Additive := sorry

/-- Small-site module pullback is additive. -/
instance etaleSmallModulePullback_additive {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [(SheafOfModules.pushforward.{u + 1} (smallChartStructureMap Y)).IsRightAdjoint]
    [(etaleSmallModulePushforward f).IsRightAdjoint] :
    (etaleSmallModulePullback f).Additive := sorry

/-- The homotopy model for π_X module pullback, in coefficient universe u + 1. -/
abbrev etalePiModuleToDerived (X : AlgebraicSpace S)
    [UnivLE.{u + 1, u + 1}] [(etalePiModulePushforward X).IsRightAdjoint] :=
  (etalePiModulePullback X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    moduleLocalization.{u + 1} (Big.ringedSite X)

/-- The unbounded total left derived module pullback of π_X. -/
abbrev etalePiModulePullbackDerived (X : AlgebraicSpace S)
    [UnivLE.{u + 1, u + 1}] [(etalePiModulePushforward X).IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor (etalePiModuleToDerived X)
      (ModuleQis.{u + 1} (ringedSite X))] :
    ModuleDerived.{u + 1} (ringedSite X) ⥤
      ModuleDerived.{u + 1} (Big.ringedSite X) :=
  Functor.totalLeftDerived (etalePiModuleToDerived X)
    (moduleLocalization.{u + 1} (ringedSite X)) (ModuleQis.{u + 1} (ringedSite X))

/-- The independent small-site pullback homotopy model, in coefficient universe u + 1. -/
abbrev etaleSmallModuleToDerived {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}]
    [(SheafOfModules.pushforward.{u + 1} (smallChartStructureMap Y)).IsRightAdjoint]
    [(etaleSmallModulePushforward f).IsRightAdjoint] :=
  (etaleSmallModulePullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    moduleLocalization.{u + 1} (ringedSite Y)

/-- The total left derived module pullback on the small étale site. -/
abbrev etaleSmallModulePullbackDerived {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}]
    [(SheafOfModules.pushforward.{u + 1} (smallChartStructureMap Y)).IsRightAdjoint]
    [(etaleSmallModulePushforward f).IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor (etaleSmallModuleToDerived f)
      (ModuleQis.{u + 1} (ringedSite X))] :
    ModuleDerived.{u + 1} (ringedSite X) ⥤ ModuleDerived.{u + 1} (ringedSite Y) :=
  Functor.totalLeftDerived (etaleSmallModuleToDerived f)
    (moduleLocalization.{u + 1} (ringedSite X)) (ModuleQis.{u + 1} (ringedSite X))

/-- Derived small-site module pullback agrees with big-site pullback followed by relocalization. -/
theorem etaleSmallModulePullbackDerived_comp {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}] [(etalePiModulePushforward X).IsRightAdjoint]
    [(SheafOfModules.pushforward.{u + 1} (smallChartStructureMap Y)).IsRightAdjoint]
    [(etaleSmallModulePushforward f).IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor (etalePiModuleToDerived X)
      (ModuleQis.{u + 1} (ringedSite X))]
    [Functor.HasLeftDerivedFunctor (etaleSmallModuleToDerived f)
      (ModuleQis.{u + 1} (ringedSite X))] :
    IsIsomorphic (etaleSmallModulePullbackDerived f)
      (etalePiModulePullbackDerived X ⋙ relocalizationModuleDerived f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Etale
