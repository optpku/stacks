module

import StacksCheckRecall
import ReasLib.RingTheory.Spectrum.Prime.ResidueFieldTensor

/-!
# Off-diagonal residue-field tensors meeting the diagonal
-/

@[expose] public section

universe u

open PrimeSpectrum Algebra.TensorProduct
open scoped TensorProduct

variable {A k : Type u} [CommRing A] [Field k]

/- Lemma 68.15.1: Let `A` be a ring and `k` a field. Let `p n`, `n ≥ 1`, be a
sequence of pairwise distinct primes of `A`, and for each `n` let
`k →+* κ(p n)` be an embedding. Then the closure of the image of the coproduct
of `Spec(κ(p n) ⊗[k] κ(p m))` over `n ≠ m` in `Spec(A ⊗[ℤ] A)` meets the
diagonal `Spec(A) ⟶ Spec(A ⊗[ℤ] A)`. -/
@[stacks 088I] #check (PrimeSpectrum.closure_offDiag_residueFieldTensor_meets_diagonal :
    ∀ {A k : Type u} [CommRing A] [Field k],
      (p : ℕ → PrimeSpectrum A) →
      Pairwise (fun n m ↦ p n ≠ p m) →
      (ι : ∀ n, k →+* (p n).asIdeal.ResidueField) →
      (closure
          (⋃ ij ∈ (Set.univ : Set ℕ).offDiag,
            Set.range (comap (Ideal.ResidueField.tensorHom (ι ij.1) (ι ij.2)))) ∩
        Set.range
          (comap (Algebra.TensorProduct.lmul' ℤ : A ⊗[ℤ] A →ₐ[ℤ] A).toRingHom)).Nonempty)
