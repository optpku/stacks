module

public import ReasLib.RingTheory.RestrictedPowerSeries.NaiveCotangent

/-! # Restricted-power-series quotient presentations -/

@[expose] public section

universe u

#check (Algebra.NaiveCotangent.Restricted.Presentation :
  ∀ (A B : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing B] [Algebra A B]
    (ι : Type u), Type u)
