module

public import Mathlib.LinearAlgebra.Prod

@[expose] public section

/-!
# The square-zero endomorphism associated to a linear map

A linear map `ρ : F₁ →ₗ[R] F₀` determines the block endomorphism
`(a, b) ↦ (0, ρ a)` of `F₁ × F₀`. This file owns that construction independently of any
dual-number interpretation.
-/

universe u v w

namespace LinearMap.TwoTerm

variable {R : Type u} [Semiring R]
variable {F₁ : Type v} {F₀ : Type w}
variable [AddCommMonoid F₁] [Module R F₁] [AddCommMonoid F₀] [Module R F₀]

/-- The block endomorphism `(a, b) ↦ (0, ρ a)` associated to a linear map `ρ`. -/
@[stacks 05CS "two-term square-zero endomorphism"]
def endomorphism (ρ : F₁ →ₗ[R] F₀) : Module.End R (F₁ × F₀) :=
  (LinearMap.inr R F₁ F₀).comp (ρ.comp (LinearMap.fst R F₁ F₀))

/-- The block endomorphism associated to `ρ` has the expected value on a pair. -/
@[simp]
theorem endomorphism_apply (ρ : F₁ →ₗ[R] F₀) (x : F₁ × F₀) :
    endomorphism ρ x = (0, ρ x.1) :=
  rfl

/-- The block endomorphism associated to a linear map is square-zero. -/
@[simp, stacks 05CS "two-term square-zero relation"]
theorem endomorphism_sq (ρ : F₁ →ₗ[R] F₀) :
    (endomorphism ρ).comp (endomorphism ρ) = 0 := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, endomorphism_apply, endomorphism_apply]
  simp

end LinearMap.TwoTerm
