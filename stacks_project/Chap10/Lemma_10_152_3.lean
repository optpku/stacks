module

public import Mathlib.RingTheory.Unramified.LocalStructure
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.152.3

@stack 00UY
-/

open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.152.3: if `R → S` is unramified and `p ⊂ R` is prime, then after an étale base
change `R → R'` with a prime `p'` over `p`, the algebra `R' ⊗[R] S` decomposes as a finite
product `A₁ × ... × Aₙ × B` such that each map `R' → Aᵢ` is surjective, the extended ideal
`p'Aᵢ` is a prime of `Aᵢ` lying over `p'`, and there is no prime of `B` lying over `p'`. -/
@[stacks 00UY]
theorem exists_surjective_factor_decomposition_of_pure_decomposition
    [Algebra.Unramified R S] (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p),
      ∃ (ι : Type (max u v)) (_ : Fintype ι) (A : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A i))
        (instAAlg : ∀ i, Algebra R' (A i)) (B : Type (max u v)) (instBComm : CommRing B)
        (instBAlg : Algebra R' B),
      ∃ _ : R' ⊗[R] S ≃ₐ[R'] ((i : ι) → A i) × B,
      ∃ r : ∀ i, p'.primesOver (A i),
      (∀ i, Function.Surjective (algebraMap R' (A i))) ∧
        (∀ i, (r i).1 = Ideal.map (algebraMap R' (A i)) p') ∧
        (∀ _ : p'.primesOver B, False) := sorry

end
