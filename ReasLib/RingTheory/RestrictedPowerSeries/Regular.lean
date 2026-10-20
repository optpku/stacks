/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.RestrictedPowerSeries
public import ReasLib.RingTheory.Ideal.RigClosed
public import ReasLib.RingTheory.Regular.RingMap

/-!
# Regularity of restricted power series over rig-closed primes
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace RestrictedPowerSeries

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- For an adic Noetherian topological ring and a rig-closed prime, the canonical
inclusion of the quotient into its tensor product with restricted power series
in a positive number of variables is a regular ring map. -/
instance tensorQuotientHom_regular (n : ℕ) [NeZero n] (p : Ideal A) [p.IsRigClosed] :
    ((Algebra.TensorProduct.includeRight :
      (A ⧸ p) →ₐ[A] RestrictedPowerSeries (Fin n) A ⊗[A] (A ⧸ p)).toRingHom).Regular :=
  sorry

/-- The residue-field fiber of restricted power series in a positive number of
variables over an adic Noetherian topological ring at a rig-closed prime is
geometrically regular over the residue field. -/
instance fiber_isGeometricallyRegular (n : ℕ) [NeZero n] (p : Ideal A)
    [p.IsRigClosed] :
    Algebra.IsGeometricallyRegular p.ResidueField
      (p.Fiber (RestrictedPowerSeries (Fin n) A)) :=
  sorry

end RestrictedPowerSeries
