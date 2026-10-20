module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

@[expose] public section

universe u v

namespace Ring.DirectLimit

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
variable (A : ι → Type v) [∀ i, CommRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (f · · ·)]

/-- Surjectivity on prime spectra of every transition in a directed system of
commutative rings implies surjectivity from the colimit spectrum to each stage. -/
theorem comap_surjective
    (hf : ∀ ⦃i j⦄ (hij : i ≤ j), Function.Surjective (PrimeSpectrum.comap (f i j hij)))
    (i : ι) : Function.Surjective (PrimeSpectrum.comap (of A (f · · ·) i)) :=
  sorry

/-- Surjectivity from a directed colimit spectrum to a stage spectrum implies
surjectivity on prime spectra of every transition out of that stage. -/
theorem comap_transition_surjective {i j : ι} (hij : i ≤ j)
    (h : Function.Surjective (PrimeSpectrum.comap (of A (f · · ·) i))) :
    Function.Surjective (PrimeSpectrum.comap (f i j hij)) :=
  sorry

end Ring.DirectLimit
