/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor presentation of Kähler differentials

@stack 00RW

Mathlib defines `KaehlerDifferential R S` as the cotangent module of the kernel of the
multiplication map `S ⊗[R] S → S`. This leaf records the source-facing tensor formula for scalar
multiples of the universal differential.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace KaehlerDifferential

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- The tensor `a ⊗ b - ab ⊗ 1` belongs to the kernel ideal defining Kähler differentials. -/
theorem tensor_sub_mul_tmul_one_mem_ideal (a b : S) :
    a ⊗ₜ[R] b - (a * b) ⊗ₜ[R] (1 : S) ∈ ideal R S := sorry

/-- Lemma 10.131.13: in the cotangent presentation of `Ω[S⁄R]`, the element `a • db` is
represented by `a ⊗ b - ab ⊗ 1`. -/
@[stacks 00RW]
theorem smul_D_apply (a b : S) :
    a • D R S b =
      (ideal R S).toCotangent
        ⟨a ⊗ₜ[R] b - (a * b) ⊗ₜ[R] (1 : S),
          tensor_sub_mul_tmul_one_mem_ideal R S a b⟩ := sorry

end KaehlerDifferential
