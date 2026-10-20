module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

universe u v

namespace PowerSeries

/-- Two formal power series over a commutative ring are equal if and only if they
become equal after extending coefficients to its total fraction ring. -/
theorem map_fractionRing_eq_iff {R : Type u} {K : Type v}
    [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
    (f g : PowerSeries R) :
    PowerSeries.map (algebraMap R K) f = PowerSeries.map (algebraMap R K) g ↔ f = g := by
  constructor
  · exact fun h => PowerSeries.map_injective (algebraMap R K)
      (IsFractionRing.injective R K) h
  · exact fun h => congrArg (PowerSeries.map (algebraMap R K)) h

end PowerSeries
