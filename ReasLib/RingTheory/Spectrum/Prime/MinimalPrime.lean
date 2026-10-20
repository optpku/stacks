module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Minimal points under spectrum maps

This leaf is the bundled `PrimeSpectrum` view of Mathlib's ideal-level
minimal-prime lifting theorem.  The ideal theorem remains the proof owner; the
bridge lets consumers work with points of `Spec` without unpacking `asIdeal`.

@stack 0CAN
-/

universe u v

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A minimal point in the image of `Spec S → Spec R` lifts to a minimal point
of `Spec S`. -/
@[stacks 0CAN "minimal point lifting along a spectrum map"]
theorem exists_isMin_comap_eq_of_mem_range (f : R →+* S) (p : PrimeSpectrum R)
    (hp : IsMin p) (hp_range : p ∈ Set.range (comap f)) :
    ∃ q : PrimeSpectrum S, IsMin q ∧ comap f q = p := sorry

end PrimeSpectrum
