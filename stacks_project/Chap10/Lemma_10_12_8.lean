/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.12.8

@stack 00DE
-/

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type x} [AddCommGroup P] [Module R P]

/- Lemma 10.12.8 is `source-facing` but recall-shaped: the owner abstraction is the canonical
linear equivalence `TensorProduct.lift.equiv`, and the textbook bijection
`Hom_R(M ⊗[R] N, P) ≃ Hom_R(M, Hom_R(N, P))` is its specialization along `RingHom.id R` followed by
inversion. -/
@[stacks 00DE "tensor-Hom equivalence"]
#check
  ((TensorProduct.lift.equiv (.id R) M N P).symm :
    (M ⊗[R] N →ₗ[R] P) ≃ₗ[R] (M →ₗ[R] N →ₗ[R] P))

/- Companion check: the forward map of this inverse specialization is the canonical curried map
`TensorProduct.curry`, sending `f : M ⊗[R] N →ₗ[R] P` to `m ↦ fun n ↦ f (m ⊗ₜ n)`. -/
@[stacks 00DE "curried tensor map"]
#check (TensorProduct.curry : (M ⊗[R] N →ₗ[R] P) → M →ₗ[R] N →ₗ[R] P)
