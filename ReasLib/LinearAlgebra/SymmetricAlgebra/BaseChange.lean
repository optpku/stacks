/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.IsTensorProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetric algebras and base change

The forward map extends the symmetric-algebra lift across scalar extension. The inverse lifts
the generators transported by the inverse module base-change equivalence.

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
    A ⊗[R] SymmetricAlgebra R M ≃ₐ[A] SymmetricAlgebra A N :=
  let forward : A ⊗[R] SymmetricAlgebra R M →ₐ[A] SymmetricAlgebra A N :=
    AlgHom.liftEquiv R A (SymmetricAlgebra R M) (SymmetricAlgebra A N)
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι A N).restrictScalars R ∘ₗ f))
  let inverse : SymmetricAlgebra A N →ₐ[A] A ⊗[R] SymmetricAlgebra R M :=
    SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι R M).baseChange A ∘ₗ h.equiv.symm.toLinearMap)
  AlgEquiv.ofAlgHom forward inverse (by sorry) (by sorry)

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
