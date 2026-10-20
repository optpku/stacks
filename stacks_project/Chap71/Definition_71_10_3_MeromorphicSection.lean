module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Sections

/-! Compatibility facade for actual localized meromorphic module sections. -/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.meromorphicSectionPresheaf :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (F : X.Modules),
    PresheafOfModules.{u + 1}
      (ringPresheaf (regularStructureSections X).localizationPresheaf))

#check (AlgebraicGeometry.AlgebraicSpace.meromorphicSectionSheaf :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (F : X.Modules),
    ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X) (meromorphicFunctionSheaf X))

#check (AlgebraicGeometry.AlgebraicSpace.meromorphicSections :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (F : X.Modules), Type (u + 1))
