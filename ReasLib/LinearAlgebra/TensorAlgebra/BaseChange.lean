/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.RingTheory.IsTensorProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor algebras and base change

The owner is an arbitrary `IsBaseChange A f`; localization and other concrete scalar-extension
models are specializations.

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

/-- Tensor algebra commutes with an arbitrary module base change.  The orientation follows
`IsBaseChange.equiv`: scalar extension of the source maps to the chosen target model. -/
@[stacks 0C6F "tensor algebra under module base change"]
noncomputable def tensorAlgebraEquiv (h : IsBaseChange A f) :
    A ⊗[R] TensorAlgebra R M ≃ₐ[A] TensorAlgebra A N :=
  AlgEquiv.ofAlgHom
    (AlgHom.liftEquiv R A (TensorAlgebra R M) (TensorAlgebra A N)
      (TensorAlgebra.lift R ((TensorAlgebra.ι A).restrictScalars R ∘ₗ f)))
    (TensorAlgebra.lift A
      ((TensorAlgebra.ι R).baseChange A ∘ₗ h.equiv.symm.toLinearMap))
    (by sorry)
    (by sorry)

/-- The tensor-algebra base-change equivalence maps a scalar multiple of a source generator to
the corresponding target generator. -/
@[simp, stacks 0C6F "tensor algebra base change on generators"]
theorem tensorAlgebraEquiv_tmul_ι (h : IsBaseChange A f) (a : A) (m : M) :
    h.tensorAlgebraEquiv (a ⊗ₜ[R] TensorAlgebra.ι R m) =
      a • TensorAlgebra.ι A (f m) := sorry

/-- The inverse tensor-algebra equivalence sends an arbitrary target generator through the
inverse module base-change equivalence. -/
@[simp, stacks 0C6F "inverse tensor algebra base change on generators"]
theorem tensorAlgebraEquiv_symm_apply_ι (h : IsBaseChange A f) (x : N) :
    h.tensorAlgebraEquiv.symm (TensorAlgebra.ι A x) =
      (TensorAlgebra.ι R).baseChange A (h.equiv.symm x) := sorry

end IsBaseChange
