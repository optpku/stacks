module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Minimal primes of local rings

This file records locality properties of quotients of local rings by minimal
prime ideals.
-/

@[expose] public section

universe u

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The quotient of a local ring by a minimal prime ideal is a local ring. -/
instance instIsLocalRingQuotientMinimalPrime (p : minimalPrimes A) :
    IsLocalRing (A ⧸ p.1) := sorry
