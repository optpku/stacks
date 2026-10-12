/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Scalar Extension of Linear Maps and Differential Operators

The lowest layer records only the commuting square for a linear map and its
scalar extension.  The differential-operator layer adds an order bound on top
of that relation, so either layer can be reused independently.
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace LinearMap.BaseChange

section BaseChange

variable {R S S' M N : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- An `R`-linear map on scalar-extended modules is an extension of `D` when the canonical
scalar-extension square commutes. -/
@[stacks 0H94]
def IsExtension (D : M →ₗ[R] N)
    (D' : S' ⊗[S] M →ₗ[R] S' ⊗[S] N) : Prop :=
  D'.comp ((TensorProduct.mk S S' M 1).restrictScalars R) =
      ((TensorProduct.mk S S' N 1).restrictScalars R).comp D

end BaseChange

section Composition

variable {R S S' M₁ M₂ M₃ : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M₁] [Module S M₁] [Module R M₁] [IsScalarTower R S M₁]
variable [AddCommGroup M₂] [Module S M₂] [Module R M₂] [IsScalarTower R S M₂]
variable [AddCommGroup M₃] [Module S M₃] [Module R M₃] [IsScalarTower R S M₃]

namespace IsExtension

/-- Compatible scalar extensions are closed under composition. -/
theorem comp {D₁ : M₁ →ₗ[R] M₂} {D₂ : M₂ →ₗ[R] M₃}
    {D₁' : S' ⊗[S] M₁ →ₗ[R] S' ⊗[S] M₂}
    {D₂' : S' ⊗[S] M₂ →ₗ[R] S' ⊗[S] M₃}
    (hD₁ : IsExtension D₁ D₁') (hD₂ : IsExtension D₂ D₂') :
    IsExtension (D₂.comp D₁) (D₂'.comp D₁') := sorry

end IsExtension

end Composition

end LinearMap.BaseChange

namespace LinearMap.IsDifferentialOperatorOfOrder.BaseChange

section BaseChange

variable {R S S' M N : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- An operator on scalar-extended modules is an extension of `D` of order `k` when the
scalar-extension square commutes and the target has the prescribed order bound. -/
@[stacks 0H94]
def IsExtension (D : M →ₗ[R] N) (k : ℕ)
    (D' : S' ⊗[S] M →ₗ[R] S' ⊗[S] N) : Prop :=
  LinearMap.BaseChange.IsExtension D D' ∧ D'.IsDifferentialOperatorOfOrder S' k

namespace IsExtension

/-- The linear-map compatibility contained in a differential-operator extension. -/
theorem commutes {D : M →ₗ[R] N} {k : ℕ}
    {D' : S' ⊗[S] M →ₗ[R] S' ⊗[S] N}
    (hD : IsExtension D k D') :
    LinearMap.BaseChange.IsExtension D D' := sorry

/-- The order bound contained in a differential-operator extension. -/
theorem order {D : M →ₗ[R] N} {k : ℕ}
    {D' : S' ⊗[S] M →ₗ[R] S' ⊗[S] N}
    (hD : IsExtension D k D') :
    D'.IsDifferentialOperatorOfOrder S' k := sorry

end IsExtension

end BaseChange

section Composition

variable {R S S' M₁ M₂ M₃ : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M₁] [Module S M₁] [Module R M₁] [IsScalarTower R S M₁]
variable [AddCommGroup M₂] [Module S M₂] [Module R M₂] [IsScalarTower R S M₂]
variable [AddCommGroup M₃] [Module S M₃] [Module R M₃] [IsScalarTower R S M₃]

namespace IsExtension

/-- Composing two scalar-extended differential operators composes their source operators and
adds their order bounds. -/
@[stacks 0H95]
theorem comp {D₁ : M₁ →ₗ[R] M₂} {D₂ : M₂ →ₗ[R] M₃} {k₁ k₂ : ℕ}
    {D₁' : S' ⊗[S] M₁ →ₗ[R] S' ⊗[S] M₂}
    {D₂' : S' ⊗[S] M₂ →ₗ[R] S' ⊗[S] M₃}
    (hD₁ : IsExtension D₁ k₁ D₁') (hD₂ : IsExtension D₂ k₂ D₂') :
    IsExtension (D₂.comp D₁) (k₁ + k₂) (D₂'.comp D₁') := sorry

end IsExtension

end Composition

end LinearMap.IsDifferentialOperatorOfOrder.BaseChange
