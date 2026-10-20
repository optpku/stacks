module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Tensor

/-!
# Tensor Multiplication by Principal Ideals

@stack 00M6

This leaf records the direct regular-element criterion for the canonical
tensor multiplication map of a principal ideal.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Ideal

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Every tensor with a principal ideal is represented by its generator tensored with one
module element. -/
theorem exists_eq_span_singleton_tmul (f : R)
    (z : (Ideal.span ({f} : Set R)) ⊗[R] M) :
    ∃ m : M, z =
      ((⟨f, Ideal.mem_span_singleton_self f⟩ : Ideal.span ({f} : Set R)) ⊗ₜ[R] m) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      exact ⟨0, by simp⟩
  | tmul x m =>
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp x.2
      have hx :
          x = r • (⟨f, Ideal.mem_span_singleton_self f⟩ : Ideal.span ({f} : Set R)) := by
        exact Subtype.ext hr.symm
      refine ⟨r • m, ?_⟩
      rw [hx, TensorProduct.smul_tmul]
  | add x y hx hy =>
      obtain ⟨mx, hx⟩ := hx
      obtain ⟨my, hy⟩ := hy
      refine ⟨mx + my, ?_⟩
      rw [hx, hy, TensorProduct.tmul_add]

/-- Stacks 00M6: if `f` acts injectively on `M`, then multiplication from
`(f) ⊗[R] M` to `M` is injective. -/
@[stacks 00M6 "principal ideal tensor multiplication"]
theorem tensorMul_span_singleton_injective {f : R}
    (hf : IsSMulRegular M f) :
    Function.Injective ((Ideal.span ({f} : Set R)).tensorMul M) := by
  intro x y hxy
  obtain ⟨mx, hx⟩ := exists_eq_span_singleton_tmul f x
  obtain ⟨my, hy⟩ := exists_eq_span_singleton_tmul f y
  rw [hx, hy] at hxy ⊢
  have hmx_my : mx = my := hf (by simpa using hxy)
  rw [hmx_my]

end Ideal
