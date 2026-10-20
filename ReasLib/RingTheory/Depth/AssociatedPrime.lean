module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.RingTheory.Depth.RegularSequence
public import ReasLib.RingTheory.Depth.SupportDim

/-!
# Depth Bounds from Associated Primes

@stack 0BK4

An associated prime bounds the local depth by the Krull dimension of its
quotient.  The theorem is placed in `Module`, which keeps the mathematical
name short while making its owner explicit.
-/

@[expose] public section

open scoped ENat

universe u v

namespace Module

/-- Lemma 10.72.9, tag `0BK4`: the depth of a finite module over a
Noetherian local ring is bounded by the dimension of every associated-prime
quotient. -/
@[stacks 0BK4]
theorem depth_le_krullDim_quotient {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    .some (moduleDepth R M) ≤ ringKrullDim (R ⧸ p) := sorry

end Module
