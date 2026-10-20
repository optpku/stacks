module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Spectrum images of split polynomial quotients

This leaf identifies the image on prime spectra of a multivariate-polynomial quotient whose
defining ideal contains a split polynomial in every variable.

@stack 0532
-/

@[expose] public section

open PrimeSpectrum
open scoped BigOperators

universe u

namespace MvPolynomial

variable {R : Type u} [CommRing R] {n : ℕ} (d : Fin n → ℕ)

/-- Lemma 15.21.4: suppose `J ⊆ R[T₁, …, Tₙ]` contains, for every `i`, the split
polynomial `∏ j, (Tᵢ - αᵢⱼ)`. Then the image of the prime spectrum of the quotient is the
zero locus of the intersection of the evaluation images of `J`. -/
@[stacks 0532]
theorem range_comap_quotient_eq_zeroLocus_iInf_eval
    (J : Ideal (MvPolynomial (Fin n) R)) (α : ∀ i : Fin n, Fin (d i) → R)
    (hJ : ∀ i : Fin n, ∏ j : Fin (d i), (X i - C (α i j)) ∈ J) :
    Set.range (comap (algebraMap R (MvPolynomial (Fin n) R ⧸ J))) =
      zeroLocus
        (⨅ k : ∀ i : Fin n, Fin (d i), Ideal.map (eval fun i ↦ α i (k i)) J) := sorry

end MvPolynomial
