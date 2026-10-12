/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

universe u

open Set

variable {R : Type u} [CommSemiring R]

/-- Every irreducible closed subset of the prime spectrum has a generic point. -/
theorem PrimeSpectrum.exists_isGenericPoint {S : Set (PrimeSpectrum R)}
    (hS : IsIrreducible S) (hSclosed : IsClosed S) :
    ∃ x, IsGenericPoint x S := sorry

/-- The canonical correspondence from a prime spectrum to its irreducible closed subsets is
bijective. -/
theorem PrimeSpectrum.pointsEquivIrreducibleCloseds_bijective (R : Type u) [CommSemiring R] :
    Function.Bijective (PrimeSpectrum.pointsEquivIrreducibleCloseds R :
      PrimeSpectrum R → (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ) := sorry

/-- The canonical correspondence sends a prime to the irreducible closed subset given by the
closure of its singleton. -/
theorem PrimeSpectrum.coe_pointsEquivIrreducibleCloseds_apply (p : PrimeSpectrum R) :
    ((OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds R p) :
      TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R)) : Set (PrimeSpectrum R)) = closure {p} := rfl
