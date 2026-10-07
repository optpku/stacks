module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Radical ideals and closed subsets of the prime spectrum

The zero-locus and vanishing-ideal maps identify radical ideals with closed subsets
of the prime spectrum of a commutative semiring.
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- Radical ideals of a commutative semiring correspond to closed subsets of its prime
spectrum via the zero-locus map, with inverse given by the vanishing ideal. -/
noncomputable def radicalIdealEquivClosed (R : Type u) [CommSemiring R] :
    {ideal : Ideal R // ideal.IsRadical} ≃
      {closedSet : Set (PrimeSpectrum R) // IsClosed closedSet} where
  toFun radicalIdeal := ⟨zeroLocus radicalIdeal.val, isClosed_zeroLocus _⟩
  invFun closedSet := ⟨vanishingIdeal closedSet.val, isRadical_vanishingIdeal _⟩
  left_inv radicalIdeal := by
    apply Subtype.ext
    exact (vanishingIdeal_zeroLocus_eq_radical radicalIdeal.val).trans
      radicalIdeal.property.radical
  right_inv closedSet := by
    apply Subtype.ext
    exact (zeroLocus_vanishingIdeal_eq_closure closedSet.val).trans
      closedSet.property.closure_eq

end PrimeSpectrum
