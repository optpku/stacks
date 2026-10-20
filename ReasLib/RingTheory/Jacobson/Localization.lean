module

public import ReasLib.RingTheory.Jacobson.Noetherian

/-!
# Jacobson away localizations

An away localization at an element of the Jacobson radical of a Noetherian ring is a
Jacobson ring. The formulation with an arbitrary localization target is the reusable owner;
`Localization.Away f` is its canonical specialization.
-/

@[expose] public section

universe u v

namespace IsJacobsonRing

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- If `f` belongs to the Jacobson radical of a Noetherian ring, every away localization at
`f` is a Jacobson ring. -/
@[stacks 0GED "Jacobson-radical form"]
theorem of_isLocalizationAway_of_mem_jacobson
    {S : Type v} [CommRing S] [Algebra A S] (f : A) [IsLocalization.Away f S]
    (hf : f ∈ Ring.jacobson A) :
    IsJacobsonRing S := sorry

/-- If `I ≤ Ring.jacobson A` and `f ∈ I`, every away localization of the
Noetherian ring `A` at `f` is a Jacobson ring. -/
@[stacks 0GED "Zariski-pair form"]
theorem of_isLocalizationAway_of_mem_of_le_jacobson
    {S : Type v} [CommRing S] [Algebra A S]
    (I : Ideal A) (hI : I ≤ Ring.jacobson A)
    (f : A) [IsLocalization.Away f S] (hf : f ∈ I) :
    IsJacobsonRing S := sorry

end IsJacobsonRing
