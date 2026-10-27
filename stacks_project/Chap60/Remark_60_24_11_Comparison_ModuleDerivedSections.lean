/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.AffineBase
public import ReasLib.AlgebraicGeometry.Scheme.Module.DerivedSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineGeometry

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CrystallineModuleDerivedSections
export AlgebraicGeometry.Scheme.Modules.DerivedSections (asSiteSheaf asSiteSheaf_additive liftSheaf liftSheaf_additive
  sheafDerivedCategory sections_additive ofComplex)
end CrystallineModuleDerivedSections
variable (A : Type u) [CommRing A]
#check (CrystallineModuleDerivedSections.baseRestriction A :
  DerivedCategory (ModuleCat.{u + 1} (CrystallineCoefficients.baseRing (Spec (.of A)))) ⥤
    DerivedCategory (ModuleCat.{u + 1} A))
