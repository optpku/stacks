/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Non-flat `ZMod` modules

@stack 00DI

Multiplication by `n` is injective on `ℤ`, but tensoring it with `ZMod n` kills the tensor of
`1` with `1`. This gives a reusable flatness counterexample for every `n > 1`.
-/

@[expose] public section

open scoped TensorProduct

namespace ZMod

/-- Multiplication by a nonzero natural number is injective on the integers. -/
@[stacks 00DI "integer scalar map is injective"]
theorem modulus_linearMap_injective (n : ℕ) (hn : n ≠ 0) :
    Function.Injective ((n : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ) := sorry

/-- Tensoring multiplication by `n` with `ZMod n` is not injective when `n > 1`. -/
@[stacks 00DI "integer scalar map is not injective after tensoring"]
theorem modulus_rTensor_not_injective (n : ℕ) (hn : 1 < n) :
    ¬ Function.Injective ((((n : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ).rTensor (ZMod n))) := by
  let f : ℤ ⊗[ℤ] ZMod n →ₗ[ℤ] ℤ ⊗[ℤ] ZMod n :=
    ((n : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ).rTensor (ZMod n)
  let z : ℤ ⊗[ℤ] ZMod n := (TensorProduct.lid ℤ (ZMod n)).symm 1
  intro h
  -- `ZMod.nontrivial` is deliberately indexed by this explicit bound.
  letI : Fact (1 < n) := ⟨hn⟩ -- proof-local temporary data
  have hz : z ≠ 0 := by
    intro hz
    have hh := congrArg (TensorProduct.lid ℤ (ZMod n)) hz
    simp [z] at hh
  apply hz
  apply h
  have hEq :
      (TensorProduct.lid ℤ (ZMod n)) (f z) = (TensorProduct.lid ℤ (ZMod n)) 0 := by
    rw [show z = (1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod n) by simp [z]]
    simp only [f, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    simp
  exact (TensorProduct.lid ℤ (ZMod n)).injective hEq

/-- For `n > 1`, `ZMod n` is not flat as an integer module. -/
@[stacks 00DI "non-flat ZMod module"]
theorem not_flat (n : ℕ) (hn : 1 < n) : ¬ Module.Flat ℤ (ZMod n) := by
  intro hflat
  apply modulus_rTensor_not_injective n hn
  apply (Module.Flat.iff_rTensor_preserves_injective_linearMap.mp hflat)
  change Function.Injective fun x : ℤ ↦ (n : ℤ) * x
  exact smul_right_injective ℤ (by exact_mod_cast Nat.ne_zero_of_lt hn)

end ZMod
