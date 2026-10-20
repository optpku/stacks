module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor Products of Multivariable Polynomial Rings

@stack 00SQ
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace MvPolynomial.TensorEquivSum

variable (R : Type u) [CommSemiring R] (σ : Type v) (ι : Type w)

/-- The left tensor factor becomes the left summand of variables. -/
@[simp, stacks 00SQ "left tensor factor under the sum-variable equivalence"]
theorem comp_includeLeft :
    ((MvPolynomial.tensorEquivSum R σ ι R).toRingHom.comp
      Algebra.TensorProduct.includeLeftRingHom) =
      (MvPolynomial.rename Sum.inl).toRingHom := by
  apply MvPolynomial.ringHom_ext <;> intro <;> simp

/-- The right tensor factor becomes the right summand of variables. -/
@[simp, stacks 00SQ "right tensor factor under the sum-variable equivalence"]
theorem comp_includeRight :
    ((MvPolynomial.tensorEquivSum R σ ι R).toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        MvPolynomial ι R →ₐ[R] MvPolynomial σ R ⊗[R] MvPolynomial ι R)) =
      (MvPolynomial.rename Sum.inr).toRingHom := by
  apply MvPolynomial.ringHom_ext <;> intro <;> simp

end MvPolynomial.TensorEquivSum
