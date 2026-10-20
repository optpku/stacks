/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed

/-!
# Restriction of algebraic-space modules to an underlying scheme

An `𝒪`-module on the algebraic space associated to a scheme over a base restricts along the
tautological identity chart to a module on that underlying scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The tautological identity chart of `ofOver U`, as an object of the canonical small étale
site. -/
def tautologicalChart {S : Scheme.{u}} (U : Over S) :
    SmallEtale.site (ofOver U) :=
  (SmallEtale.fromPresentation (ofOver U)).obj (smallEtaleSite.mk (𝟙 (ofOver U)))

/-- The chart presentation is a dense subsite of the canonical small étale site. -/
instance fromPresentation_isDenseSubsite {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (SmallEtale.fromPresentation X).IsDenseSubsite
      (smallEtaleTopology X) (SmallEtale.topology X) where
  isCoverDense' :=
    let e : SmallEtale.site X ≌ smallEtaleSite X :=
      CategoryTheory.Equivalence.mk
        (SmallEtale.toPresentation X)
        (SmallEtale.fromPresentation X)
        (eqToIso (SmallEtale.toPresentation_fromPresentation X)).symm
        (eqToIso (SmallEtale.fromPresentation_toPresentation X))
    inferInstanceAs (e.inverse.IsCoverDense (SmallEtale.topology X))
  isLocallyFull' :=
    let e : SmallEtale.site X ≌ smallEtaleSite X :=
      CategoryTheory.Equivalence.mk
        (SmallEtale.toPresentation X)
        (SmallEtale.fromPresentation X)
        (eqToIso (SmallEtale.toPresentation_fromPresentation X)).symm
        (eqToIso (SmallEtale.fromPresentation_toPresentation X))
    inferInstanceAs (e.inverse.IsLocallyFull (SmallEtale.topology X))
  isLocallyFaithful' :=
    let e : SmallEtale.site X ≌ smallEtaleSite X :=
      CategoryTheory.Equivalence.mk
        (SmallEtale.toPresentation X)
        (SmallEtale.fromPresentation X)
        (eqToIso (SmallEtale.toPresentation_fromPresentation X)).symm
        (eqToIso (SmallEtale.fromPresentation_toPresentation X))
    inferInstanceAs (e.inverse.IsLocallyFaithful (SmallEtale.topology X))
  functorPushforward_mem_iff {U R} :=
    (SmallEtale.fromPresentation_topology_iff (U := U) R).symm

/-- Precomposition with the reverse comparison preserves sheaves of types. -/
instance toPresentation_isContinuous {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Functor.IsContinuous (SmallEtale.toPresentation X)
      (SmallEtale.topology X) (smallEtaleTopology X) :=
  let e : SmallEtale.site X ≌ smallEtaleSite X :=
    CategoryTheory.Equivalence.mk
      (SmallEtale.toPresentation X)
      (SmallEtale.fromPresentation X)
      (eqToIso (SmallEtale.toPresentation_fromPresentation X)).symm
      (eqToIso (SmallEtale.fromPresentation_toPresentation X))
  (@CategoryTheory.Equivalence.eq_inducedTopology_of_isDenseSubsite
      (SmallEtale.site X) _ (SmallEtale.topology X)
      (smallEtaleSite X) _ (smallEtaleTopology X) e
      (fromPresentation_isDenseSubsite X)) ▸
    inferInstanceAs
      (e.functor.IsContinuous (SmallEtale.topology X)
        (e.inverse.inducedTopology (SmallEtale.topology X)))

/-- Identity scheme projections from the chart presentation to the canonical small étale
realization. -/
def toPresentationSchemeProjection {S : Scheme.{u}} (X : AlgebraicSpace S) :
    SmallEtale.toPresentation X ⋙ smallEtaleToScheme X ⟶ SmallEtale.toScheme X where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

/-- Identity comparison of global-sections structure sheaves along the chart presentation. -/
def toPresentationStructureMap {S : Scheme.{u}} (X : AlgebraicSpace S) :
    SmallEtale.structureSheaf X ⟶
      ((SmallEtale.toPresentation X).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology X) (smallEtaleTopology X)).obj (structureSheaf X) :=
  Scheme.Site.structureSheafMap
    (SmallEtale.topology X) (smallEtaleTopology X)
    (SmallEtale.toScheme X) (smallEtaleToScheme X)
    (SmallEtale.toPresentation X) (toPresentationSchemeProjection X)
    (SmallEtale.structurePresheaf_isSheaf X) (structurePresheaf_isSheaf X)

/-- Compare modules on the chart presentation with modules on the canonical small étale
site. -/
def toSmallEtaleModules {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.Modules ⥤ SmallEtale.Modules X :=
  SheafOfModules.pushforward (toPresentationStructureMap X)

/-- Restriction of an `𝒪_{ofOver U}`-module to the underlying scheme of `U`. -/
def restrictToScheme {S : Scheme.{u}} (U : Over S) :
    (ofOver U).Modules ⥤ U.left.Modules :=
  toSmallEtaleModules (ofOver U) ⋙
    SmallEtale.Modules.toScheme (tautologicalChart U)

/-- Restriction of an algebraic-space module to the underlying scheme of an étale chart. -/
def restrictToEtaleScheme {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    X.Modules ⥤ U.left.left.Modules :=
  @restrictFunctor S (ofOver U.left) X U.hom U.prop ⋙ restrictToScheme U.left

end AlgebraicGeometry.AlgebraicSpace.Modules
