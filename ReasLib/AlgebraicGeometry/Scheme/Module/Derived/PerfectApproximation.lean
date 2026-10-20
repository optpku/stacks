/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A perfect approximation of `E` supported on `T` through degree `m` consists of a perfect
derived `𝒪_X`-module supported on `T` mapping isomorphically on cohomology above `m` and
epimorphically in degree `m`. -/
def HasPerfectApproximation {X : Scheme.{u}} (T : TopologicalSpace.Closeds X)
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (m : ℤ) : Prop :=
  ∃ P : RingedSpace.ModuleDerived X.toRingedSpace,
    RingedSpace.ModuleDerived.IsPerfect P ∧
      RingedSpace.ModuleDerived.IsSupportedOn P T ∧
        ∃ α : P ⟶ E.obj,
          (∀ i : ℤ, m < i →
            IsIso (RingedSpace.ModuleDerived.cohomologySheafMap α i)) ∧
          Epi (RingedSpace.ModuleDerived.cohomologySheafMap α m)

/-- The existential characterization of a perfect approximation supported on a closed subset. -/
theorem hasPerfectApproximation_iff {X : Scheme.{u}} (T : TopologicalSpace.Closeds X)
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (m : ℤ) :
    HasPerfectApproximation T E m ↔
      ∃ P : RingedSpace.ModuleDerived X.toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect P ∧
          RingedSpace.ModuleDerived.IsSupportedOn P T ∧
            ∃ α : P ⟶ E.obj,
              (∀ i : ℤ, m < i →
                IsIso (RingedSpace.ModuleDerived.cohomologySheafMap α i)) ∧
              Epi (RingedSpace.ModuleDerived.cohomologySheafMap α m) := sorry

namespace HasPerfectApproximation

/-- Perfect approximation is preserved when the quasicoherent target is replaced by an
isomorphic derived object. -/
theorem of_iso {X : Scheme.{u}} {T : TopologicalSpace.Closeds X}
    {E F : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)} {m : ℤ}
    (hE : HasPerfectApproximation T E m) (e : E ≅ F) :
    HasPerfectApproximation T F m := sorry

end HasPerfectApproximation

end AlgebraicGeometry.Scheme
