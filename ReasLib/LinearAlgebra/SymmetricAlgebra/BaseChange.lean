module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.IsTensorProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetric algebras and base change

@stack 0C6F
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace IsBaseChange

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {N : Type x} [AddCommMonoid N] [Module R N] [Module A N]
variable [IsScalarTower R A N]
variable {f : M →ₗ[R] N}

/-- Symmetric algebra commutes with an arbitrary module base change. -/
@[stacks 0C6F "symmetric algebra under module base change"]
noncomputable def symmetricAlgebraEquiv (h : IsBaseChange A f) :
    A ⊗[R] SymmetricAlgebra R M ≃ₐ[A] SymmetricAlgebra A N := sorry

/-- The symmetric-algebra base-change equivalence on source generators. -/
@[simp, stacks 0C6F "symmetric algebra base change on generators"]
theorem symmetricAlgebraEquiv_tmul_ι (h : IsBaseChange A f) (a : A) (m : M) :
    h.symmetricAlgebraEquiv (a ⊗ₜ[R] SymmetricAlgebra.ι R M m) =
      a • SymmetricAlgebra.ι A N (f m) := sorry

/-- The inverse symmetric-algebra equivalence on arbitrary target generators. -/
@[simp, stacks 0C6F "inverse symmetric algebra base change on generators"]
theorem symmetricAlgebraEquiv_symm_apply_ι (h : IsBaseChange A f) (x : N) :
    h.symmetricAlgebraEquiv.symm (SymmetricAlgebra.ι A N x) =
      (SymmetricAlgebra.ι R M).baseChange A (h.equiv.symm x) := sorry

end IsBaseChange
