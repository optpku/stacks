/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Quotient.Endomorphism
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Endomorphisms detected modulo ideal multiples

An endomorphism which is the identity modulo `J M` fixes `I M` when `I * J = 0`. This
multiplicative hypothesis is the reusable core; disjoint ideals supply it when the left ideal is
two-sided.

@stack 0H7M
-/

@[expose] public section

universe u v

namespace LinearMap

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- If `I * J = 0`, an endomorphism which is the identity modulo `J M` fixes `I M` pointwise. -/
@[stacks 0H7M "ideal-multiple fixed points from a quotient identity"]
theorem eq_on_smul_top_of_mul_eq_bot
    {I J : Ideal R} (hIJ : I * J = ⊥) (a : M →ₗ[R] M)
    (hQ : ∀ x : M,
      (Submodule.mkQ (J • (⊤ : Submodule R M))) (a x) =
        (Submodule.mkQ (J • (⊤ : Submodule R M))) x) :
    ∀ x ∈ (I • (⊤ : Submodule R M)), a x = x := by
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m _
    have hd : a m - m ∈ J • (⊤ : Submodule R M) :=
      (Submodule.Quotient.eq (J • (⊤ : Submodule R M))).mp (hQ m)
    have hzero : r • (a m - m) = 0 := by
      have hmem : r • (a m - m) ∈ (I * J) • (⊤ : Submodule R M) := by
        rw [Submodule.mul_smul]
        exact Submodule.smul_mem_smul hr hd
      simpa [hIJ] using hmem
    rw [← sub_eq_zero, a.map_smul, ← smul_sub, hzero]
  · intro x y hx hy
    rw [a.map_add, hx, hy]

/-- Disjoint ideals give the multiplicative vanishing needed by
`eq_on_smul_top_of_mul_eq_bot`. -/
@[stacks 0H7M "disjoint ideal-multiple fixed points"]
theorem eq_on_smul_top_of_inf_eq_bot
    {I J : Ideal R} [I.IsTwoSided]
    (hIJ : I ⊓ J = ⊥) (a : M →ₗ[R] M)
    (hQ : ∀ x : M,
      (Submodule.mkQ (J • (⊤ : Submodule R M))) (a x) =
        (Submodule.mkQ (J • (⊤ : Submodule R M))) x) :
    ∀ x ∈ (I • (⊤ : Submodule R M)), a x = x :=
  eq_on_smul_top_of_mul_eq_bot
    (bot_unique (Ideal.mul_le_inf.trans_eq hIJ)) a hQ

end LinearMap
