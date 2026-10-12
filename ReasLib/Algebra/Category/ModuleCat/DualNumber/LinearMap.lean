/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.DualNumber.SquareZero
public import ReasLib.LinearAlgebra.LinearMap.TwoTerm

@[expose] public section

/-!
# Dual-number modules attached to a linear map

This file is the thin bridge interpreting the generic two-term square-zero endomorphism attached
to `ρ : F₁ →ₗ[R] F₀` as a module over the dual numbers.
-/

universe u v w

namespace ModuleCat.DualNumber

open scoped DualNumber

variable {R : Type u} [CommRing R]
variable {F₁ : Type v} {F₀ : Type w}
variable [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₀] [Module R F₀]

/-- The dual-number module associated to a linear map through its canonical square-zero
endomorphism. -/
@[stacks 05CS "module associated to a linear map"]
def ofLinearMap (ρ : F₁ →ₗ[R] F₀) :
    ModuleCat.{max v w} (_root_.DualNumber R) :=
  ofSquareZero (R := R) (LinearMap.TwoTerm.endomorphism ρ)
    (LinearMap.TwoTerm.endomorphism_sq ρ)

end ModuleCat.DualNumber
