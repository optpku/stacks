/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Stalk
public import ReasLib.CategoryTheory.DerivedCategory.Concentrated.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- A derived module is locally concentrated in one degree when every point has an open
neighborhood on which all derived stalks are concentrated in one common degree. -/
def IsLocallyConcentrated (E : ModuleDerived X) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ n : ℤ, ∀ y : X, y ∈ U →
    DerivedCategory.concentrated (ModuleCat (X.presheaf.stalk y)) n (Stalk.obj E y)

/-- The neighborhoodwise characterization of local concentration in one degree. -/
theorem isLocallyConcentrated_iff (E : ModuleDerived X) :
    IsLocallyConcentrated E ↔
      ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ n : ℤ, ∀ y : X, y ∈ U →
        DerivedCategory.concentrated (ModuleCat (X.presheaf.stalk y)) n
          (Stalk.obj E y) := sorry

namespace IsLocallyConcentrated

/-- Local concentration supplies a concentration degree at each individual stalk. -/
theorem «at» {E : ModuleDerived X} (hE : IsLocallyConcentrated E) (x : X) :
    ∃ n : ℤ, DerivedCategory.concentrated (ModuleCat (X.presheaf.stalk x)) n
      (Stalk.obj E x) := sorry

end IsLocallyConcentrated

end AlgebraicGeometry.RingedSpace.ModuleDerived
