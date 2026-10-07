module

public import ReasLib.RingTheory.Flatness.ZMod
import StacksCheckRecall

@[expose] public section

/-!
# Remark 10.12.11
@stack 00DH

-/

@[stacks 00DH]
#check show
    Function.Exact (0 : Unit →ₗ[ℤ] ℤ) ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) ∧
      ¬ Function.Exact ((0 : Unit →ₗ[ℤ] ℤ).rTensor (ZMod 2))
        (((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)).rTensor (ZMod 2))
  from by
    constructor
    · rw [LinearMap.exact_zero_iff_injective]
      change Function.Injective fun x : ℤ ↦ 2 * x
      simpa [smul_eq_mul] using
        smul_right_injective ℤ (r := (2 : ℤ)) (by decide)
    · rw [LinearMap.rTensor_zero, LinearMap.exact_zero_iff_injective]
      have h := ZMod.modulus_rTensor_not_injective 2 (by decide)
      norm_num at h ⊢
      exact h

@[stacks 00DH "flat modules preserve tensor exactness"]
#check @Module.Flat.rTensor_exact

@[stacks 00DH "tensor exactness characterizes flatness"]
#check @Module.Flat.iff_rTensor_exact
