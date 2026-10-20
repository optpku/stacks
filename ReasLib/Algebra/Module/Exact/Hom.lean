/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness Detected by Linear Hom

The two criteria below package the covariant and contravariant left-exactness
tests for a pair of composable linear maps.  They are stated over an arbitrary
ring by viewing the induced Hom maps as `ℤ`-linear maps.

@stack 0582
-/

@[expose] public section

universe uR u1 u2 u3 u4 u5

namespace LinearMap

variable {R : Type uR} [Ring R]
variable {M1 : Type u1} {M2 : Type u2} {M3 : Type u3}
variable [AddCommGroup M1] [AddCommGroup M2] [AddCommGroup M3]
variable [Module R M1] [Module R M2] [Module R M3]

/-- Lemma 10.10.1 (1): exactness ending in a surjection is equivalent to exactness of every
contravariant Hom sequence. -/
@[stacks 0582 "(1), contravariant Hom criterion"]
theorem exact_surjective_iff_forall_lcomp
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3) :
    (Function.Exact f g ∧ Function.Surjective g) ↔
      ∀ (N : Type (max u2 u3 u4)) [AddCommGroup N] [Module R N],
        Function.Injective (lcomp ℤ N g) ∧
          Function.Exact (lcomp ℤ N g) (lcomp ℤ N f) := sorry

/-- Lemma 10.10.1 (2): exactness beginning in an injection is equivalent to exactness of every
covariant Hom sequence. -/
@[stacks 0582 "(2), covariant Hom criterion"]
theorem injective_exact_iff_forall_compRight
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3) :
    (Function.Injective f ∧ Function.Exact f g) ↔
      ∀ (N : Type (max u1 u2 u5)) [AddCommGroup N] [Module R N],
        let F : (N →ₗ[R] M1) →ₗ[ℤ] N →ₗ[R] M2 := compRight ℤ f
        let G : (N →ₗ[R] M2) →ₗ[ℤ] N →ₗ[R] M3 := compRight ℤ g
        Function.Injective F ∧ Function.Exact F G := sorry

end LinearMap
