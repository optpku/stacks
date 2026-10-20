module

public import ReasLib.RingTheory.RestrictedPowerSeries

@[expose] public section

universe u v

open RestrictedPowerSeries

#check (RestrictedPowerSeries.component :
  ∀ {σ : Type u} {A : Type v} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A],
    (I : RestrictedPowerSeries.OpenIdeal A) →
      RestrictedPowerSeries σ A →+* MvPolynomial σ (A ⧸ I.1))
