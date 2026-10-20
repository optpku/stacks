/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ClosedSubset.Derived.Supported
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.ClosedSubset

/-- Closed-subset module sheaves use their standard unbounded derived category. -/
instance closedSubsetModulesHasDerivedCategory (X : Scheme.{u})
    (Z : TopologicalSpace.Closeds X) :
    HasDerivedCategory (Modules X.toRingedSpace.ringCatSheaf Z) :=
  HasDerivedCategory.standard _

end SheafOfModules.ClosedSubset

end
