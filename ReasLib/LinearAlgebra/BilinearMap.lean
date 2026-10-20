/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Scalar extension of bilinear maps

This file supplies the heterogeneous bilinear analogue of `LinearMap.baseChange`.  It extends a
map `M →ₗ[R] N →ₗ[R] P` to the scalar extensions of all three modules and retains the expected
pure-tensor formula.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x y

namespace LinearMap

variable {R : Type u} {S : Type v}
variable {M : Type w} {N : Type x} {P : Type y}
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- Scalar extension of a heterogeneous bilinear map. -/
@[stacks 00DV "scalar extension of a bilinear map"]
def baseChange₂ (f : M →ₗ[R] N →ₗ[R] P) :
    (S ⊗[R] M) →ₗ[S] (S ⊗[R] N) →ₗ[S] (S ⊗[R] P) :=
  TensorProduct.AlgebraTensorModule.lift <|
    LinearMap.toSpanSingleton S
      (M →ₗ[R] (S ⊗[R] N) →ₗ[S] (S ⊗[R] P))
      ((LinearMap.baseChangeHom R S N P).comp f)

/-- Scalar extension evaluates on pure tensors by multiplying the scalar coefficients and
applying the original bilinear map. -/
@[simp]
theorem baseChange₂_tmul (f : M →ₗ[R] N →ₗ[R] P)
    (r s : S) (x : M) (y : N) :
    f.baseChange₂ (r ⊗ₜ[R] x) (s ⊗ₜ[R] y) =
      (r * s) ⊗ₜ[R] f x y := sorry

end LinearMap
