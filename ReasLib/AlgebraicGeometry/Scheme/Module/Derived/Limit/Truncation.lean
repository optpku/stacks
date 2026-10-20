/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Truncation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Affine
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory.Truncation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- A compatible map from a derived module with quasi-coherent cohomology to the limit of its
canonical lower-truncation tower is an isomorphism. -/
theorem lowerTruncationComparison_isIso
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    {K : RingedSpace.ModuleDerived X.toRingedSpace} {c : E.obj ⟶ K}
    (hc : Lower.Comparison.Exists E.obj c) :
    IsIso c := sorry

end AlgebraicGeometry.Scheme

end
