/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Compact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Generation
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Every quasi-compact quasi-separated scheme has a perfect weak generator of its derived
category of modules with quasicoherent cohomology. -/
theorem exists_isPerfect_isWeakGenerator :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X],
      ∃ P : Scheme.ModuleDerived.Quasicoherent X,
        RingedSpace.ModuleDerived.IsPerfect P.obj ∧ CategoryTheory.IsWeakGenerator P := sorry

/-- A perfect weak generator of the derived category of modules with quasicoherent cohomology
on a quasi-compact quasi-separated scheme classically generates its compact objects. -/
theorem isClassicalGeneratorOfCompacts {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (G : Scheme.ModuleDerived.Quasicoherent X)
    (hG_perfect : RingedSpace.ModuleDerived.IsPerfect G.obj)
    (hG_generator : CategoryTheory.IsWeakGenerator G) :
    CategoryTheory.IsClassicalGeneratorOfCompacts G := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
