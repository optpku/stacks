module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Derived

universe u

/- The promoted owner preserves the complete supported-module API. -/
#check (CategoryTheory.ModuleCat.SupportedOn.derivedAdjunction :
  ∀ {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A)),
    CategoryTheory.ModuleCat.SupportedOn.derivedInclusion T ⊣
      CategoryTheory.ModuleCat.SupportedOn.derivedSections T)
