module

public import ReasLib.RingTheory.Ideal.Quotient.FormallyEtale
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

@[expose] public section

universe u

namespace IsLocalRing

/-- The residue map of a local ring that is not a field is not flat. -/
theorem residue_not_flat {R : Type u} [CommRing R] [IsLocalRing R]
    (h : ¬ IsField R) : ¬ (residue R).Flat := sorry

end IsLocalRing
