/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Homology.Bounded
public import ReasLib.CategoryTheory.InverseSystem.Positive

/-!
# Cohomology of positive inverse systems

This module applies bounded cohomology stagewise to positive inverse systems of bounded
coherent derived objects on a scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.ModuleDerived.BoundedSystem

variable {X : Scheme.{v}}

/-- The positive inverse system obtained by taking degree-`p` cohomology at every stage of a
bounded coherent inverse system and then forgetting to `X.Modules`. -/
noncomputable abbrev cohomology
    (K : PNatInverseSystem
      (@DerivedCategory.Bounded.CohomologyIn X.Modules _ _
        (AlgebraicGeometry.Scheme.Modules.schemeModulesHasDerivedCategory X)
        (SheafOfModules.isCoherent X.ringCatSheaf))) (p : ℤ) :
    PNatInverseSystem X.Modules :=
  K ⋙ (@DerivedCategory.Bounded.CohomologyIn.Homology.functor X.Modules _ _
    (AlgebraicGeometry.Scheme.Modules.schemeModulesHasDerivedCategory X)
    (SheafOfModules.isCoherent X.ringCatSheaf) p) ⋙
    (SheafOfModules.isCoherent X.ringCatSheaf).ι

/-- A stage of the degree-`p` cohomology system is the cohomology of the corresponding
bounded-derived stage. -/
theorem cohomology_stage
    (K : PNatInverseSystem
      (@DerivedCategory.Bounded.CohomologyIn X.Modules _ _
        (AlgebraicGeometry.Scheme.Modules.schemeModulesHasDerivedCategory X)
        (SheafOfModules.isCoherent X.ringCatSheaf)))
    (p : ℤ) (n : ℕ+) :
    (cohomology K p).stage n =
      ((@DerivedCategory.Bounded.CohomologyIn.Homology.functor X.Modules _ _
        (AlgebraicGeometry.Scheme.Modules.schemeModulesHasDerivedCategory X)
        (SheafOfModules.isCoherent X.ringCatSheaf) p).obj (K.stage n)).obj := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.BoundedSystem
