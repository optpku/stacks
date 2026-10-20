/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.DualNumber.LinearMap
public import ReasLib.Algebra.Category.ModuleCat.DualNumber.SquareZero.Quotient
public import ReasLib.LinearAlgebra.LinearMap.TwoTerm.Quotient

@[expose] public section

/-!
# Epsilon quotients of dual-number modules attached to linear maps

This file combines the generic two-term cokernel calculation with the dual-number interpretation.
Consumers see only the original linear map `ρ`; the square-zero endomorphism and its proof are
encapsulated by the owner API.
-/

universe u v w

open scoped DualNumber

namespace ModuleCat.DualNumber.OfLinearMap

variable {R : Type u} [CommRing R]
variable {F₁ : Type v} {F₀ : Type w}
variable [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₀] [Module R F₀]

/-- Modulo multiplication by `ε`, the dual-number module attached to `ρ` is
`F₁ × (F₀ ⧸ LinearMap.range ρ)`. -/
@[stacks 05CS "epsilon quotient of a linear-map module"]
noncomputable def epsQuotientEquiv (ρ : F₁ →ₗ[R] F₀) :
    epsQuotient (ofLinearMap ρ) ≃ₗ[R]
      F₁ × (F₀ ⧸ LinearMap.range ρ) :=
  (OfSquareZero.epsQuotientEquiv
      (LinearMap.TwoTerm.endomorphism ρ)
      (LinearMap.TwoTerm.endomorphism_sq ρ)).trans
    (LinearMap.TwoTerm.cokernelEquiv ρ)

set_option backward.isDefEq.respectTransparency false in
/-- The epsilon-quotient equivalence attached to `ρ` sends a representative to its first
coordinate and the quotient class of its second coordinate. -/
@[simp]
theorem epsQuotientEquiv_mk (ρ : F₁ →ₗ[R] F₀) (x : F₁ × F₀) :
    epsQuotientEquiv ρ (Submodule.Quotient.mk x) =
      (x.1, Submodule.Quotient.mk x.2) := by
  change LinearMap.TwoTerm.cokernelEquiv ρ
      (OfSquareZero.epsQuotientEquiv
        (LinearMap.TwoTerm.endomorphism ρ)
        (LinearMap.TwoTerm.endomorphism_sq ρ)
        (Submodule.Quotient.mk x)) =
    (x.1, Submodule.Quotient.mk x.2)
  rw [OfSquareZero.epsQuotientEquiv_mk,
    LinearMap.TwoTerm.cokernelEquiv_mk]

/-- The inverse epsilon-quotient equivalence attached to `ρ` sends `(a, [b])` to `[(a, b)]`. -/
@[simp]
theorem epsQuotientEquiv_symm_apply_mk
    (ρ : F₁ →ₗ[R] F₀) (a : F₁) (b : F₀) :
    (epsQuotientEquiv ρ).symm (a, Submodule.Quotient.mk b) =
      (Submodule.Quotient.mk (a, b) : epsQuotient (ofLinearMap ρ)) := by
  apply (epsQuotientEquiv ρ).injective
  simp

end ModuleCat.DualNumber.OfLinearMap
