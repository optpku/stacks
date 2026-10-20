module

public import ReasLib.RingTheory.RestrictedPowerSeries.Quotient

@[expose] public section

universe u

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [CommRing A] [TopologicalSpace A]

#check (RingHom.IsClosedQuotientOfRestrictedPowerSeries : (B →+* A) → Prop)
