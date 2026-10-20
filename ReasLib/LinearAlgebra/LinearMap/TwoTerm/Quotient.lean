/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import ReasLib.LinearAlgebra.LinearMap.TwoTerm

@[expose] public section

/-!
# The cokernel of a two-term square-zero endomorphism

For `ρ : F₁ →ₗ[R] F₀`, the cokernel of the endomorphism `(a, b) ↦ (0, ρ a)` is explicitly
`F₁ × (F₀ ⧸ LinearMap.range ρ)`. Both directions are quotient lifts, so the equivalence does not
choose representatives from a surjectivity proof.
-/

universe u v w

namespace LinearMap.TwoTerm

variable {R : Type u} [Ring R]
variable {F₁ : Type v} {F₀ : Type w}
variable [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₀] [Module R F₀]

/-- The canonical map from `F₁ × F₀` to `F₁ × (F₀ ⧸ LinearMap.range ρ)`. -/
@[stacks 05CS "two-term cokernel projection"]
def cokernelProjection (ρ : F₁ →ₗ[R] F₀) :
    F₁ × F₀ →ₗ[R] F₁ × (F₀ ⧸ LinearMap.range ρ) :=
  (LinearMap.fst R F₁ F₀).prod
    ((LinearMap.range ρ).mkQ.comp (LinearMap.snd R F₁ F₀))

/-- The two-term cokernel projection has the expected value on a pair. -/
@[simp]
theorem cokernelProjection_apply (ρ : F₁ →ₗ[R] F₀) (x : F₁ × F₀) :
    cokernelProjection ρ x = (x.1, Submodule.Quotient.mk x.2) :=
  rfl

/-- The range of the two-term square-zero endomorphism is killed by its cokernel projection. -/
theorem range_le_ker_cokernelProjection (ρ : F₁ →ₗ[R] F₀) :
    LinearMap.range (endomorphism ρ) ≤ LinearMap.ker (cokernelProjection ρ) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  simp

/-- The two-term endomorphism and its explicit cokernel projection form an exact pair. -/
@[stacks 05CS "exact two-term cokernel sequence"]
theorem exact_endomorphism_cokernelProjection (ρ : F₁ →ₗ[R] F₀) :
    Function.Exact (endomorphism ρ) (cokernelProjection ρ) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    have hx₁ : x.1 = 0 := congrArg Prod.fst hx
    have hx₂ : Submodule.Quotient.mk x.2 = 0 := congrArg Prod.snd hx
    rw [Submodule.Quotient.mk_eq_zero] at hx₂
    obtain ⟨y, hy⟩ := hx₂
    refine ⟨(y, 0), ?_⟩
    rw [endomorphism_apply]
    ext
    · exact hx₁.symm
    · exact hy
  · exact range_le_ker_cokernelProjection ρ

/-- The explicit two-term cokernel projection is surjective. -/
theorem cokernelProjection_surjective (ρ : F₁ →ₗ[R] F₀) :
    Function.Surjective (cokernelProjection ρ) := by
  rintro ⟨a, q⟩
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨(a, b), rfl⟩

/-- The map from the cokernel of the two-term endomorphism to the explicit product quotient. -/
@[stacks 05CS "two-term cokernel forward map"]
def cokernelForward (ρ : F₁ →ₗ[R] F₀) :
    ((F₁ × F₀) ⧸ LinearMap.range (endomorphism ρ)) →ₗ[R]
      F₁ × (F₀ ⧸ LinearMap.range ρ) :=
  (LinearMap.range (endomorphism ρ)).liftQ
    (cokernelProjection ρ) (range_le_ker_cokernelProjection ρ)

/-- The forward cokernel map sends a representative to its two visible coordinates. -/
@[simp]
theorem cokernelForward_mk (ρ : F₁ →ₗ[R] F₀) (x : F₁ × F₀) :
    cokernelForward ρ (Submodule.Quotient.mk x) =
      (x.1, Submodule.Quotient.mk x.2) :=
  rfl

/-- The map from `F₀` into the two-term cokernel through the second coordinate. -/
def cokernelInrMap (ρ : F₁ →ₗ[R] F₀) :
    F₀ →ₗ[R] ((F₁ × F₀) ⧸ LinearMap.range (endomorphism ρ)) :=
  (LinearMap.range (endomorphism ρ)).mkQ.comp (LinearMap.inr R F₁ F₀)

/-- The range of `ρ` is killed by the second-coordinate map into the two-term cokernel. -/
theorem range_le_ker_cokernelInrMap (ρ : F₁ →ₗ[R] F₀) :
    LinearMap.range ρ ≤ LinearMap.ker (cokernelInrMap ρ) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  change Submodule.Quotient.mk (0, ρ x) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨(x, 0), by rw [endomorphism_apply]⟩

/-- The second-coordinate map into the two-term cokernel, descended to `F₀ / range ρ`. -/
def cokernelInr (ρ : F₁ →ₗ[R] F₀) :
    (F₀ ⧸ LinearMap.range ρ) →ₗ[R]
      ((F₁ × F₀) ⧸ LinearMap.range (endomorphism ρ)) :=
  (LinearMap.range ρ).liftQ (cokernelInrMap ρ)
    (range_le_ker_cokernelInrMap ρ)

/-- The explicit inverse from the product quotient to the cokernel of the two-term endomorphism. -/
@[stacks 05CS "two-term cokernel inverse map"]
def cokernelInverse (ρ : F₁ →ₗ[R] F₀) :
    F₁ × (F₀ ⧸ LinearMap.range ρ) →ₗ[R]
      ((F₁ × F₀) ⧸ LinearMap.range (endomorphism ρ)) :=
  ((LinearMap.range (endomorphism ρ)).mkQ.comp
      (LinearMap.inl R F₁ F₀)).coprod (cokernelInr ρ)

/-- The inverse cokernel map sends `(a, [b])` to `[(a, b)]`. -/
@[simp]
theorem cokernelInverse_mk (ρ : F₁ →ₗ[R] F₀) (a : F₁) (b : F₀) :
    cokernelInverse ρ (a, Submodule.Quotient.mk b) =
      Submodule.Quotient.mk (a, b) := by
  change Submodule.Quotient.mk (a, 0) + Submodule.Quotient.mk (0, b) =
    Submodule.Quotient.mk (a, b)
  rw [← Submodule.Quotient.mk_add]
  simp

/-- The explicit inverse followed by the forward map is the identity. -/
theorem cokernelForward_comp_inverse (ρ : F₁ →ₗ[R] F₀) :
    (cokernelForward ρ).comp (cokernelInverse ρ) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨a, q⟩
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp

/-- The forward map followed by the explicit inverse is the identity. -/
theorem cokernelInverse_comp_forward (ρ : F₁ →ₗ[R] F₀) :
    (cokernelInverse ρ).comp (cokernelForward ρ) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp

/-- The cokernel of the two-term endomorphism is explicitly
`F₁ × (F₀ ⧸ LinearMap.range ρ)`. -/
@[stacks 05CS "two-term endomorphism cokernel"]
def cokernelEquiv (ρ : F₁ →ₗ[R] F₀) :
    ((F₁ × F₀) ⧸ LinearMap.range (endomorphism ρ)) ≃ₗ[R]
      F₁ × (F₀ ⧸ LinearMap.range ρ) :=
  LinearEquiv.ofLinear (cokernelForward ρ) (cokernelInverse ρ)
    (cokernelForward_comp_inverse ρ) (cokernelInverse_comp_forward ρ)

/-- The cokernel equivalence sends a representative to its two visible coordinates. -/
@[simp]
theorem cokernelEquiv_mk (ρ : F₁ →ₗ[R] F₀) (x : F₁ × F₀) :
    cokernelEquiv ρ (Submodule.Quotient.mk x) =
      (x.1, Submodule.Quotient.mk x.2) :=
  cokernelForward_mk ρ x

/-- The inverse cokernel equivalence sends `(a, [b])` to `[(a, b)]`. -/
@[simp]
theorem cokernelEquiv_symm_apply_mk (ρ : F₁ →ₗ[R] F₀) (a : F₁) (b : F₀) :
    (cokernelEquiv ρ).symm (a, Submodule.Quotient.mk b) =
      Submodule.Quotient.mk (a, b) :=
  cokernelInverse_mk ρ a b

end LinearMap.TwoTerm
