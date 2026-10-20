/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.Basic
public import ReasLib.LinearAlgebra.TensorProduct.RightModule
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential Operators and Tensor Products

This leaf records preservation of differential-operator order under tensoring
an `R`-linear map on the right.  The required right-factor scalar actions are
the opt-in instances from `TensorProduct.Right`; they are not global because a
tensor product can carry genuinely distinct actions from its two factors.

@stack 0G37
-/

@[expose] public section

open scoped TensorProduct TensorProduct.Right

universe u v w x y

namespace LinearMap.IsDifferentialOperatorOfOrder

section RightTensor

variable {R : Type u} {A : Type v} {B : Type w}
variable {M : Type x} {M' : Type y} {N : Type*}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra R B]
variable [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
variable [Module A M] [Module A M'] [Module B N]
variable [Module R M] [Module R M'] [Module R N]
variable [IsScalarTower R A M] [IsScalarTower R A M'] [IsScalarTower R B N]

/-- Lemma 10.133.13 (Tag 0G37): tensoring an order-`k` differential operator
on the right preserves its order bound over the tensor-product algebra. -/
@[stacks 0G37]
theorem rTensor {D : M →ₗ[R] M'} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder A k) :
    (D.rTensor N).IsDifferentialOperatorOfOrder (A ⊗[R] B) k := sorry

end RightTensor

end LinearMap.IsDifferentialOperatorOfOrder
