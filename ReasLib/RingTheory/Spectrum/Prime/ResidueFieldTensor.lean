/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.Ideal.ResidueField.TensorProduct

/-!
# Off-diagonal residue-field tensors meeting the diagonal

An infinite sequence of pairwise distinct primes with residue fields receiving
a common field gives an off-diagonal tensor-spectrum closure intersecting the
diagonal.
-/

@[expose] public section

universe u

open PrimeSpectrum Algebra.TensorProduct
open scoped TensorProduct

namespace PrimeSpectrum

variable {A k : Type u} [CommRing A] [Field k]

/-- The closure of the off-diagonal residue-field tensor spectra meets the diagonal in `Spec (A ⊗[ℤ] A)`. -/
theorem closure_offDiag_residueFieldTensor_meets_diagonal
    (p : ℕ → PrimeSpectrum A) (hp : Pairwise fun n m ↦ p n ≠ p m)
    (ι : ∀ n, k →+* (p n).asIdeal.ResidueField) :
    (closure
        (⋃ ij ∈ (Set.univ : Set ℕ).offDiag,
          Set.range (comap (Ideal.ResidueField.tensorHom (ι ij.1) (ι ij.2)))) ∩
      Set.range
        (comap (Algebra.TensorProduct.lmul' ℤ : A ⊗[ℤ] A →ₐ[ℤ] A).toRingHom)).Nonempty :=
  sorry

end PrimeSpectrum
