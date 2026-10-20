module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.Local

@[expose] public section

/-!
# Localization of Complete Intersection Local Rings

This module records the prime-local stability of the complete-intersection local-ring property.
-/

universe u

namespace IsCompleteIntersectionLocalRing

variable {A : Type u} [CommRing A] [IsCompleteIntersectionLocalRing A]

/-- A complete-intersection local ring remains complete-intersection after localization at any
prime ideal. -/
@[stacks 09Q4]
theorem localizationAtPrime (p : PrimeSpectrum A) :
    IsCompleteIntersectionLocalRing (Localization.AtPrime p.asIdeal) := sorry

end IsCompleteIntersectionLocalRing

namespace IsLocalCompleteIntersectionRing

variable {A : Type u} [CommRing A]

section Noetherian

variable [IsNoetherianRing A]

/-- Lemma 23.8.7 (Tag 09Q5): a Noetherian ring is a local complete intersection if and only if
all of its localizations at maximal ideals are complete-intersection local rings. -/
@[stacks 09Q5]
theorem iff_forall_maximal :
    IsLocalCompleteIntersectionRing A ↔
      ∀ m : MaximalSpectrum A,
        IsCompleteIntersectionLocalRing (Localization.AtPrime m.asIdeal) := sorry

end Noetherian

/-- A local complete intersection ring is complete-intersection local at every maximal ideal. -/
@[stacks 09Q5 "maximal-local consequence of a local complete intersection"]
theorem atMaximal [IsLocalCompleteIntersectionRing A] (m : MaximalSpectrum A) :
    IsCompleteIntersectionLocalRing (Localization.AtPrime m.asIdeal) := sorry

section Noetherian

variable [IsNoetherianRing A]

/-- The maximal-local criterion constructs the local complete intersection structure. -/
@[stacks 09Q5 "maximal-local complete-intersection constructor"]
theorem of_localizationAtMaximal
    (hMax : ∀ m : MaximalSpectrum A,
      IsCompleteIntersectionLocalRing (Localization.AtPrime m.asIdeal)) :
    IsLocalCompleteIntersectionRing A := sorry

end Noetherian

end IsLocalCompleteIntersectionRing
