/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealComplement
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- This bridge preserves the historical helper import surface for downstream Chapter files. -/
#check AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomologyFunctor
#check AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomology
#check AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomologyFunctorZero_isomorphic
#check CategoryTheory.DerivedCategory.LocalCohomology.supportedCohomology
#check CategoryTheory.DerivedCategory.LocalCohomology.supportedCohomology_isIdealPowerTorsion
#check CategoryTheory.DerivedCategory.LocalCohomology.supportedCohomology_isomorphic
