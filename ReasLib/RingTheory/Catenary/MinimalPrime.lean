module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Quotient

@[expose] public section

/-!
# Catenarity and Minimal Primes

These criteria reduce catenarity and universal catenarity to the irreducible
components represented by minimal-prime quotients.

@stack 0AUP
-/

universe u v

section

variable {R : Type u} [CommRing R]

/-- Lemma 10.105.8 (1): a Noetherian ring is catenary exactly when all of its minimal-prime
quotients are catenary. -/
@[stacks 0AUP]
theorem isCatenaryRing_iff_forall_quotient_by_minimalPrime [IsNoetherianRing R] :
    IsCatenaryRing R ↔ ∀ p ∈ minimalPrimes R, IsCatenaryRing (R ⧸ p) := sorry

/-- Lemma 10.105.8 (2): a Noetherian ring is universally catenary exactly when all of its
minimal-prime quotients are universally catenary. -/
@[stacks 0AUP]
theorem universallyCatenaryRing_iff_forall_quotient_by_minimalPrime [IsNoetherianRing R] :
    UniversallyCatenaryRing.{u, v} R ↔
      ∀ p ∈ minimalPrimes R, UniversallyCatenaryRing.{u, v} (R ⧸ p) := sorry

end
