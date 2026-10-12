/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Remark_87_28_1_Universal_property_restricted_power_series_RestrictedPowerSeries

/-!
# Adic and Noetherian instances for restricted power series

Restricted power series in finitely many variables over a Noetherian adic ring
remain Noetherian and adic, so primes of `A{x₁, …, xₙ}` may carry `IsRigClosed`.
-/

@[expose] public section

universe u

namespace RestrictedPowerSeries

/-- Restricted power series in finitely many variables over a Noetherian adic
ring remain an adic topological ring. -/
instance instIsAdicRing (n : ℕ) {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] :
    TopologicalRing.IsAdicRing (RestrictedPowerSeries (Fin n) A) :=
  sorry

/-- Restricted power series in finitely many variables over a Noetherian adic
ring remain Noetherian. -/
instance instIsNoetherianRing (n : ℕ) {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] :
    IsNoetherianRing (RestrictedPowerSeries (Fin n) A) :=
  sorry

end RestrictedPowerSeries
