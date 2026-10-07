module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Top-dimensional minimal primes

The top-dimensional locus among the minimal primes is a canonical set of
ideals.  Naming it avoids rebuilding the same set comprehension in
equidimensionality and Hilbert--Samuel arguments.

@stack 0BWX
-/

universe u

namespace minimalPrimes

/-- The minimal primes whose quotient has the same Krull dimension as the
ambient ring. -/
@[stacks 0BWX "top-dimensional minimal primes"]
def topDim (R : Type u) [CommRing R] : Set (Ideal R) :=
  {p | p ∈ _root_.minimalPrimes R ∧ ringKrullDim (R ⧸ p) = ringKrullDim R}

/-- Membership in the top-dimensional minimal-prime locus. -/
@[simp, stacks 0BWX "membership in the top-dimensional minimal primes"]
theorem mem_topDim_iff {R : Type u} [CommRing R] (p : Ideal R) :
    p ∈ topDim R ↔
      p ∈ _root_.minimalPrimes R ∧ ringKrullDim (R ⧸ p) = ringKrullDim R := sorry

/-- A Noetherian ring has only finitely many top-dimensional minimal primes. -/
@[stacks 0BWX "finiteness of top-dimensional minimal primes"]
theorem topDim_finite (R : Type u) [CommRing R] [IsNoetherianRing R] :
    (topDim R).Finite := sorry

end minimalPrimes
