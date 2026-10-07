module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.ClosedSupport

open CategoryTheory

universe u

/- The promoted closed-support comparison API remains available under its established names. -/
#check (CategoryTheory.ModuleCat.SupportedOn.comparisonIsIso :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ),
    IsIso (ModuleCat.SupportedOn.comparison T hT K i))
