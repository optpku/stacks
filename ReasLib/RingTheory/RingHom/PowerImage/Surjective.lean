module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import ReasLib.RingTheory.RingHom.PowerImage
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Positive-power-surjective ring homomorphisms

This leaf owns the general ring-hom property that every target element has a positive power in
the source image.  Spectral consequences live in a separate `Spectrum` leaf.
-/

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Every target element has some positive power in the image of a ring homomorphism. -/
def IsPowerSurjective (f : R →+* S) : Prop :=
  ∀ x : S, ∃ e : ℕ+, PowerImage.InRange f x e

/-- The bundled positive-exponent predicate and the raw natural-exponent formulation are
equivalent. -/
theorem isPowerSurjective_iff_forall_pow_mem_range (f : R →+* S) :
    f.IsPowerSurjective ↔ ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ f.range := sorry

/-- Positive powers in the source image make the ring homomorphism integral. -/
theorem isIntegral_of_isPowerSurjective (f : R →+* S) (hpow : f.IsPowerSurjective) :
    f.IsIntegral := sorry

end RingHom
