/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen

/-!
# Bases of nonvanishing opens of positive tensor powers

This file defines the family of nonvanishing opens arising from global sections of positive
tensor powers of an invertible module and records its affine basis refinement.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The family of nonvanishing opens of global sections of positive tensor powers of an
invertible module. -/
noncomputable def positiveTensorPowerNonvanishingOpens
    (L : X.Modules) [hL : Invertible L] : Set X.Opens :=
  {U | ∃ n : ℕ+, ∃ s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤),
    U = hL.nonvanishingOpen s}

/-- An open belongs to `positiveTensorPowerNonvanishingOpens L` exactly when it is the
nonvanishing open of a global section of some positive tensor power of `L`. -/
theorem mem_positiveTensorPowerNonvanishingOpens
    (L : X.Modules) [hL : Invertible L] (U : X.Opens) :
    U ∈ positiveTensorPowerNonvanishingOpens L ↔
      ∃ n : ℕ+, ∃ s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤),
        U = hL.nonvanishingOpen s := sorry

/-- If the nonvanishing opens of global sections of positive tensor powers of an invertible
module form a topological basis, then the affine members of that family also form a basis. -/
theorem isBasis_affine_positiveTensorPowerNonvanishingOpens
    (L : X.Modules) [Invertible L]
    (hBasis : TopologicalSpace.Opens.IsBasis (positiveTensorPowerNonvanishingOpens L)) :
    TopologicalSpace.Opens.IsBasis
      {U : X.Opens | U ∈ positiveTensorPowerNonvanishingOpens L ∧ IsAffineOpen U} := sorry

end AlgebraicGeometry.Scheme.Modules
