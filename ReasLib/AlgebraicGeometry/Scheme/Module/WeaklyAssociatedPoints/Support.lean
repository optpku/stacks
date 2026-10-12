/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Topology.MinimalSpecialization

/-!
# Support of weakly associated points

This file compares the associated-point and weakly-associated-point loci of a scheme module with
its support.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Every associated point of a scheme module is weakly associated to the module. -/
theorem associatedPoints_subset_weakAss (ℱ : X.Modules) :
    associatedPoints ℱ ⊆ ℱ.weakAss := sorry

/-- Every weakly associated point of a scheme module lies in its support. -/
theorem weakAss_subset_support (ℱ : X.Modules) :
    ℱ.weakAss ⊆ moduleSupport ℱ := sorry

/-- Every minimal specialization point of the support of a quasicoherent scheme module is
weakly associated to the module. -/
theorem minimalSpecializationPoints_support_subset_weakAss
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    X.minimalSpecializationPoints (moduleSupport ℱ) ⊆ ℱ.weakAss := sorry

end AlgebraicGeometry.Scheme.Modules
