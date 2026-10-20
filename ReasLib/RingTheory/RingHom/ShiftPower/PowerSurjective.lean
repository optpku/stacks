module

public import ReasLib.RingTheory.RingHom.PowerImage.Surjective
public import ReasLib.RingTheory.RingHom.ShiftPower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Positive-power surjectivity for shift-power maps

This leaf bridges the shifted-polynomial generation predicate to the canonical
positive-power-surjectivity property of a ring homomorphism.
-/

@[expose] public section

universe u v

namespace RingHom.ShiftPower

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Shift-power generation implies the canonical positive-power-surjectivity property. -/
@[stacks 09EF "shift-power generation is power-surjective"]
theorem isPowerSurjective
    (f : R →+* S) (hgen : IsGenerated f) :
    f.IsPowerSurjective := sorry

end RingHom.ShiftPower
