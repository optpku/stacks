/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InverseSystem.Cohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.ModuleDerived.BoundedSystem

variable {X : Scheme.{v}}

#check (cohomology :
  PNatInverseSystem
      (@DerivedCategory.Bounded.CohomologyIn X.Modules _ _
        (AlgebraicGeometry.Scheme.Modules.schemeModulesHasDerivedCategory X)
        (SheafOfModules.isCoherent X.ringCatSheaf)) → ℤ →
    PNatInverseSystem X.Modules)

#check (cohomology_stage :
  ∀ (K : PNatInverseSystem
      (@DerivedCategory.Bounded.CohomologyIn X.Modules _ _
        (AlgebraicGeometry.Scheme.Modules.schemeModulesHasDerivedCategory X)
        (SheafOfModules.isCoherent X.ringCatSheaf)))
    (p : ℤ) (n : ℕ+),
    (cohomology K p).stage n =
      ((@DerivedCategory.Bounded.CohomologyIn.Homology.functor X.Modules _ _
        (AlgebraicGeometry.Scheme.Modules.schemeModulesHasDerivedCategory X)
        (SheafOfModules.isCoherent X.ringCatSheaf) p).obj (K.stage n)).obj)

end AlgebraicGeometry.Scheme.ModuleDerived.BoundedSystem
