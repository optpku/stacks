/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.FormallyEtale
public import ReasLib.Algebra.Module.DifferentialOperator.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

open scoped TensorProduct

variable {R S S' : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']

section FormallyEtale

variable {M N : Type u}
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Algebra.FormallyEtale S S']

/-
Remark 51.19.4: Lemmas 51.19.1 and 51.19.3 can be upgraded from derivations to
higher-order differential operators using formally étale extension and
finite-order composition, as in Algebra, Lemma 10.150.8 and Remark 10.150.9.
The following checks record these algebraic ingredients, not a new theorem
about local or scheme cohomology. The source postpones stating and proving
a precise higher-order cohomology lemma until it is needed.
-/
@[stacks 0EC8]
#check (LinearMap.IsDifferentialOperatorOfOrder.BaseChange.FormallyEtale.existsUnique_extension :
  ∀ {D : M →ₗ[R] N} {k : ℕ}, D.IsDifferentialOperatorOfOrder S k →
    ∃! D' : S' ⊗[S] M →ₗ[R] S' ⊗[S] N,
      LinearMap.IsDifferentialOperatorOfOrder.BaseChange.IsExtension D k D')

#check (DifferentialOperator.FiniteOrderEndomorphisms.FormallyEtale.existsUnique_ringHom :
  ∃! F : DifferentialOperator.finiteOrderEndomorphisms (R := R) (S := S) (M := M) →+*
    DifferentialOperator.finiteOrderEndomorphisms (R := R) (S := S') (M := S' ⊗[S] M),
    DifferentialOperator.FiniteOrderEndomorphisms.BaseChange.IsExtensionMap F)

end FormallyEtale

section Composition

variable {M₁ M₂ M₃ : Type u}
variable [AddCommGroup M₁] [Module S M₁] [Module R M₁] [IsScalarTower R S M₁]
variable [AddCommGroup M₂] [Module S M₂] [Module R M₂] [IsScalarTower R S M₂]
variable [AddCommGroup M₃] [Module S M₃] [Module R M₃] [IsScalarTower R S M₃]

#check (LinearMap.IsDifferentialOperatorOfOrder.BaseChange.IsExtension.comp :
  ∀ {D₁ : M₁ →ₗ[R] M₂} {D₂ : M₂ →ₗ[R] M₃} {k₁ k₂ : ℕ}
    {D₁' : S' ⊗[S] M₁ →ₗ[R] S' ⊗[S] M₂}
    {D₂' : S' ⊗[S] M₂ →ₗ[R] S' ⊗[S] M₃},
    LinearMap.IsDifferentialOperatorOfOrder.BaseChange.IsExtension D₁ k₁ D₁' →
    LinearMap.IsDifferentialOperatorOfOrder.BaseChange.IsExtension D₂ k₂ D₂' →
    LinearMap.IsDifferentialOperatorOfOrder.BaseChange.IsExtension
      (D₂.comp D₁) (k₁ + k₂) (D₂'.comp D₁'))

end Composition
