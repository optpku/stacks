/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Derived global sections restricted to derived `𝒪_X`-modules whose homology is
quasi-coherent in every degree. -/
noncomputable abbrev globalSections (X : Scheme.{u}) :
    DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⥤
      DerivedCategory (ModuleCat (Scheme.globalSectionsRing X)) :=
  (DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
    RingedSpace.moduleDerivedGlobalSections X.toRingedSpace

/-- For an affine scheme `Spec A`, derived global sections of complexes with
quasi-coherent homology, regarded as complexes of `A`-modules. -/
noncomputable abbrev affineGlobalSections (A : CommRingCat.{u}) :
    DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace) ⥤
      DerivedCategory (ModuleCat A) :=
  globalSections (Spec A) ⋙
    ModuleCat.derivedRestrictionOfScalars (Scheme.ΓSpecIso A).inv.hom

end AlgebraicGeometry.Scheme.DerivedQCoh
