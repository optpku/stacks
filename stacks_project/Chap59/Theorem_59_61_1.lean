/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.Splitting.TFAE
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

-- Local instance justification (noncanonical choice): select the right extension-field action; global registration conflicts with the left action when the tensor factors coincide.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Theorem 59.61.1: finite central simplicity is equivalent to the standard
six-way splitting and matrix-algebra characterizations. -/
@[stacks 03R2] #check (CSA.splitting_tfae :
  List.TFAE
    [ FiniteDimensional k A ∧ Algebra.IsCentral k A ∧ IsSimpleRing A,
      FiniteDimensional k A ∧ Subalgebra.center k A = ⊥ ∧
        Nontrivial A ∧ ∀ I : Ideal A, I.IsTwoSided → I = ⊥ ∨ I = ⊤,
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k)),
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] SeparableClosure k) ≃ₐ[SeparableClosure k]
          Matrix (Fin n) (Fin n) (SeparableClosure k)),
      ∃ (k' : Type v) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k')
        (_ : IsGalois k k') (n : ℕ),
        n ≠ 0 ∧ Nonempty ((A ⊗[k] k') ≃ₐ[k'] Matrix (Fin n) (Fin n) k'),
      ∃ (n : ℕ), n ≠ 0 ∧ ∃ (D : Type v) (_ : DivisionRing D) (_ : Algebra k D)
        (_ : FiniteDimensional k D) (_ : Algebra.IsCentral k D),
        Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) D) ])

end

end
