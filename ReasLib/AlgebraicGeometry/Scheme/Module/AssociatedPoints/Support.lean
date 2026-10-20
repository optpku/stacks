/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Topology.MinimalSpecialization
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Empty

/-!
# Associated points and support of scheme modules

This file relates the stalkwise associated points of a scheme module to its support.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Every associated point of a quasi-coherent module on a scheme lies in its support. -/
theorem associatedPoints_subset_support (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    associatedPoints ℱ ⊆ moduleSupport ℱ := by
  intro x hx
  rw [mem_associatedPoints_iff] at hx
  rw [mem_moduleSupport_iff]
  by_contra hsupport
  push Not at hsupport
  have hstalk : Subsingleton (RingedSpace.stalkModuleCat ℱ x : Type u) := ⟨fun m n ↦ by
    rw [hsupport m, hsupport n]⟩
  exact (@not_isAssociatedPrime_of_subsingleton
    (X.presheaf.stalk x) inferInstance
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (RingedSpace.stalkModuleCat ℱ x : Type u) inferInstance inferInstance hstalk)
    (associatedPrimesOfModule_subset_associatedPrimes
      (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) hx)

/-- A point associated to a quasi-coherent module on a scheme belongs to its support. -/
theorem mem_moduleSupport_of_mem_associatedPoints (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (x : X) (hx : x ∈ associatedPoints ℱ) :
    x ∈ moduleSupport ℱ :=
  associatedPoints_subset_support ℱ hx

/-- Every point minimal under specialization in the support of a quasi-coherent module on a
locally Noetherian scheme is an associated point of the module. -/
theorem minimalSpecializationPoints_support_subset_associatedPoints
    [IsLocallyNoetherian X] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    X.minimalSpecializationPoints (moduleSupport ℱ) ⊆ associatedPoints ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
