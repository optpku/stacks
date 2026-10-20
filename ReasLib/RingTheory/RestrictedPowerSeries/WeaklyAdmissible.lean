module

public import ReasLib.RingTheory.RestrictedPowerSeries
public import ReasLib.RingTheory.Topology.WeaklyAdmissible

/-!
# Weak admissibility of restricted power series
-/

@[expose] public section

universe u

namespace RestrictedPowerSeries

/-- Restricted power series in finitely many variables over a weakly admissible
ring remain weakly admissible. -/
instance instIsWeaklyAdmissibleRing
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {r : ℕ} :
    TopologicalRing.IsWeaklyAdmissibleRing (RestrictedPowerSeries (Fin r) A) :=
  sorry

end RestrictedPowerSeries
