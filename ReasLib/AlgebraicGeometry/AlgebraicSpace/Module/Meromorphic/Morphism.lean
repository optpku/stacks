/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.Morphism
public import Mathlib.RingTheory.Localization.Module

/-!
# Morphisms of meromorphic module sheaves

A morphism of module sheaves induces a morphism of their localized presheaves
and hence of their sheaves of meromorphic sections. The analogous construction
on a ringed site uses localization at a compatible system of denominators and
module sheafification.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Modules
open PresheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A morphism of module sheaves induces a morphism of meromorphic-section
presheaves by localizing its section maps. -/
noncomputable def meromorphicSectionPresheafMap {X : AlgebraicSpace S}
    {F G : X.Modules} (φ : F ⟶ G) :
    meromorphicSectionPresheaf X F ⟶ meromorphicSectionPresheaf X G where
  app U := ModuleCat.ofHom
    (LinearMap.extendScalarsOfIsLocalization ((regularStructureSections X).obj U)
      ((regularStructureSections X).localizationPresheaf.obj U)
      ((LocalizedModule.map ((regularStructureSections X).obj U)
        ((liftModuleMap φ).val.app U).hom).restrictScalars
          ((commStructureSheafLift X).obj.obj U)))
  naturality := sorry

/-- The component of the induced meromorphic-section presheaf morphism is the
localization of the original section map. -/
theorem meromorphicSectionPresheafMap_app {X : AlgebraicSpace S}
    {F G : X.Modules} (φ : F ⟶ G) (U : (smallEtaleSite X)ᵒᵖ)
    (x : meromorphicSectionObj X F U) :
    (meromorphicSectionPresheafMap φ).app U x =
      LocalizedModule.map ((regularStructureSections X).obj U)
        ((liftModuleMap φ).val.app U).hom x :=
  rfl

/-- Sheafification of the localized section maps gives a morphism between the
sheaves of meromorphic sections. -/
noncomputable def meromorphicSectionSheafMap {X : AlgebraicSpace S}
    {F G : X.Modules} (φ : F ⟶ G) :
    meromorphicSectionSheaf X F ⟶ meromorphicSectionSheaf X G :=
  (moduleSheafification (smallEtaleTopology X)
      (regularStructureSections X).localizationPresheaf).map
    (meromorphicSectionPresheafMap φ)

/-- The induced morphism of meromorphic-section sheaves is the module
sheafification of the localized presheaf morphism. -/
theorem meromorphicSectionSheafMap_def {X : AlgebraicSpace S}
    {F G : X.Modules} (φ : F ⟶ G) :
    meromorphicSectionSheafMap φ =
      (moduleSheafification (smallEtaleTopology X)
          (regularStructureSections X).localizationPresheaf).map
        (meromorphicSectionPresheafMap φ) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
