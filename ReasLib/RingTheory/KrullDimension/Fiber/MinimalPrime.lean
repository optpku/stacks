/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Dimensions of minimal-prime fiber components

This leaf names the pointwise condition that every irreducible component of a
residue-field fiber has positive Krull dimension.  It is stated over an
arbitrary base prime, leaving closed-fiber specializations to applications.
-/

universe u v

namespace Algebra.Fiber

/-- A residue-field fiber has positive-dimensional minimal-prime components
when the quotient by each of its minimal primes has Krull dimension at least
`1`. -/
@[stacks 04GG "positive-dimensional minimal-prime fiber components"]
def minimalPrimesPositiveDimensional
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) : Prop :=
  ∀ q : PrimeSpectrum (p.asIdeal.Fiber S),
    q.asIdeal ∈ minimalPrimes (p.asIdeal.Fiber S) →
      1 ≤ ringKrullDim ((p.asIdeal.Fiber S) ⧸ q.asIdeal)

end Algebra.Fiber
