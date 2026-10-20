/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor Multiplication by Ideals

This leaf owns the canonical multiplication map from the tensor product of an ideal with a
module.  Flatness, `Tor`, and local flatness criteria can use this map without repeatedly
expanding its `TensorProduct.lift` definition.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Ideal

variable {R : Type u} [CommSemiring R]

/-- The canonical multiplication map `I ⊗[R] M →ₗ[R] M` induced by the inclusion `I → R`. -/
@[stacks 00M6 "ideal tensor multiplication"]
def tensorMul (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] :
    I ⊗[R] M →ₗ[R] M :=
  TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)

/-- The ideal tensor multiplication map sends a pure tensor to the corresponding scalar action. -/
@[simp]
theorem tensorMul_tmul (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M]
    (x : I) (m : M) :
    I.tensorMul M (x ⊗ₜ[R] m) = x.1 • m := by
  simp [tensorMul]

end Ideal
