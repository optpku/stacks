/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Tactic.CrossRefAttribute

/-!
# Residuation for Colon Ideals

Ideal multiplication by `J` is left adjoint to taking the colon by `J`.
-/

@[expose] public section

universe u

namespace Ideal

section Semiring

variable {R : Type u} [Semiring R]

/-- Multiplication by an ideal and taking its colon form a Galois connection. -/
@[stacks 05K8 "ideal multiplication-colon residuation"]
theorem mul_le_iff_le_colon {I J K : Ideal R} :
    K * J ≤ I ↔ K ≤ I.colon J := by
  constructor
  · intro h k hk
    rw [Submodule.mem_colon]
    intro j hj
    exact h (Ideal.mul_mem_mul hk hj)
  · intro h
    rw [Ideal.mul_le]
    intro k hk j hj
    exact Submodule.mem_colon.mp (h hk) j hj

/-- The counit of multiplication-colon residuation. -/
@[stacks 05K8 "colon ideal multiplication counit"]
theorem colon_mul_le (I J : Ideal R) : (I.colon J) * J ≤ I :=
  mul_le_iff_le_colon.mpr le_rfl

end Semiring

section CommSemiring

variable {R : Type u} [CommSemiring R]

/-- Multiplying a colon ideal back by its denominator ideal lands in the numerator. -/
@[stacks 05K8 "multiplication by a colon ideal"]
theorem mul_colon_le (I J : Ideal R) : J * (I.colon J) ≤ I := by
  simpa [mul_comm] using colon_mul_le I J

end CommSemiring

end Ideal
