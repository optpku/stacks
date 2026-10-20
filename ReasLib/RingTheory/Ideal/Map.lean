module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing ideal powers under ring maps

This leaf isolates the elementary ideal-theoretic fact that a vanishing power
remains zero after mapping an ideal.  It is independent of quotients,
localization, and universe lifts.
-/

@[expose] public section

universe u v

namespace Ideal

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]

/-- A ring homomorphism sends a zero power of an ideal to a zero power of its image. -/
theorem map_pow_eq_bot (f : R →+* S) (I : Ideal R) (n : ℕ)
    (hI : I ^ n = ⊥) :
    (I.map f) ^ n = ⊥ := sorry

/-- The image of a nilpotent ideal under a ring homomorphism is nilpotent. -/
theorem isNilpotent_map (f : R →+* S) {I : Ideal R} (hI : IsNilpotent I) :
    IsNilpotent (I.map f) := sorry

end Ideal
