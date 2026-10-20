module

public import ReasLib.RingTheory.Localization.Specializing

@[expose] public section

universe u

/- A typed compatibility check for the specializing localization API. -/
#check (Localization.specializing :
  ∀ {A : Type u} [CommRing A], A → Ideal A → Type u)
