module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.RestrictedPowerSeries
public import ReasLib.RingTheory.Topology.Adic.Complete

/-!
# Adic and Noetherian restricted power series
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
