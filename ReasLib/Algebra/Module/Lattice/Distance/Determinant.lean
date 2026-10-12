/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Lattice.Distance.Properties

/-!
# Determinants and lattice distance

@stack 02MI

This leaf compares the additive distance between a lattice and its image under a linear
automorphism with the order of vanishing of the determinant.
-/

@[expose] public section

universe u v w

namespace Submodule

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [FiniteDimensional K V] [Ring.KrullDimLE 1 R]

/-- Multiplicative companion to Lemma 10.121.7: exponentiating the lattice distance gives the
canonical multiplicative order of the determinant. -/
@[stacks 02MI "multiplicative companion"]
theorem exp_latticeDistance_map_eq_ordFrac_det
    (φ : V ≃ₗ[K] V) (M : Submodule R V) [IsLattice K M] :
    WithZero.exp (latticeDistance M
      (M.map ((φ.restrictScalars R) : V →ₗ[R] V))) =
      Ring.ordFrac R (LinearEquiv.det φ : K) := sorry

/-- Lemma 10.121.7: the lattice distance from `M` to its image under `φ` is the additive order
of vanishing of `LinearEquiv.det φ`. -/
@[stacks 02MI]
theorem latticeDistance_map_eq_log_ordFrac_det
    (φ : V ≃ₗ[K] V) (M : Submodule R V) [IsLattice K M] :
    latticeDistance M (M.map ((φ.restrictScalars R) : V →ₗ[R] V)) =
      WithZero.log (Ring.ordFrac R (LinearEquiv.det φ : K)) := sorry

end Submodule
