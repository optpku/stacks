module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Retrocompact opens in prime spectra

@stack 00F6

This leaf packages the finite-basic-open and finitely-generated-ideal
descriptions of a retrocompact open subset of a prime spectrum.
-/

@[expose] public section

open Set TopologicalSpace

universe u

namespace PrimeSpectrum

/-- Lemma 10.29.1: for an open subset of a prime spectrum, retrocompactness,
quasi-compactness, a finite principal-basic-open presentation, and a
finitely-generated-ideal presentation are equivalent. -/
@[stacks 00F6]
theorem retrocompact_open_tfae {R : Type u} [CommSemiring R]
    {U : Set (PrimeSpectrum R)} (hU : IsOpen U) :
    List.TFAE
      [ IsRetrocompact U
      , IsCompact U
      , ∃ t : Finset R,
          U = ⋃ f ∈ t, (basicOpen f : Set (PrimeSpectrum R))
      , ∃ I : Ideal R, I.FG ∧
          U = (zeroLocus (I : Set R))ᶜ
      ] := sorry

end PrimeSpectrum
