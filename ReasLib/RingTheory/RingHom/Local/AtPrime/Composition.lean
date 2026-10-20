module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Local.AtPrime

/-!
# Composition and injectivity of prime-localized ring maps

This leaf provides the composition-level bridge needed when an essentially
finite type target is presented as a localization of a finite type model.

@stack 0GS6
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace RingHom

variable {A : Type u} {C : Type v} {B : Type w}
variable [CommRing A] [CommRing C] [CommRing B] [IsLocalRing B]

/-- Injectivity of a composite map survives localization at the source prime
over the closed point of a local target. -/
@[stacks 0GS6 "injectivity after localizing a finite model"]
theorem localRingHomAt.injective_of_comp
    (f : A →+* C) (g : C →+* B)
    (h_injective : Function.Injective (g.comp f)) :
    Function.Injective
      (f.localRingHomAt (PrimeSpectrum.comap g (closedPoint B))) := sorry

/-- An injective map into a local ring remains injective on the corresponding
prime-localized source and target rings. -/
@[stacks 0GS6 "injectivity at a local target"]
theorem localRingHomAt.injective (f : A →+* B)
    (h_injective : Function.Injective f) :
    Function.Injective (f.localRingHomAt (closedPoint B)) := sorry

end RingHom
