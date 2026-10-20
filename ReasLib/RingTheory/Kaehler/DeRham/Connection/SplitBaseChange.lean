/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection.Scalar
public import ReasLib.RingTheory.Kaehler.DeRham.Connection.QuotientBaseChange
public import ReasLib.LinearAlgebra.UniversallyInjective
public import Mathlib.Algebra.Homology.Homotopy

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace Connection

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {A' : Type u} [CommRing A'] {B' : Type v} [CommRing B']
variable [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
variable [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
variable {Ω' : Type v} [AddCommGroup Ω'] [Module B' Ω'] [Module A' Ω']
variable [IsScalarTower A' B' Ω'] [Module B Ω'] [IsScalarTower B B' Ω']
variable {M : Type v} [AddCommGroup M] [Module B M]

variable (π : Ω[B⁄A] →ₗ[B] Ω) (hπ : Function.Surjective π)
variable (δ : DifferentialOperator.DeRham.Family A B Ω[B⁄A])
variable (hδ : DifferentialOperator.DeRham.IsDifferential (KaehlerDifferential.D A B) δ)
variable (hcondition : DifferentialOperator.DeRham.KernelCondition π δ)
variable (π' : Ω[B'⁄A'] →ₗ[B'] Ω') (hπ' : Function.Surjective π')
variable (δ' : DifferentialOperator.DeRham.Family A' B' Ω[B'⁄A'])
variable (hδ' : DifferentialOperator.DeRham.IsDifferential (KaehlerDifferential.D A' B') δ')
variable (hcondition' : DifferentialOperator.DeRham.KernelCondition π' δ')
variable (C : ExteriorCalculus (π.compDer (KaehlerDifferential.D A B))
  (KaehlerDifferential.DeRham.descendedFamily π hπ δ hδ hcondition))
variable (C' : ExteriorCalculus (π'.compDer (KaehlerDifferential.D A' B'))
  (KaehlerDifferential.DeRham.descendedFamily π' hπ' δ' hδ' hcondition'))
variable (φ : Ω →ₗ[B] Ω')
variable (hsquare : ∀ ω, φ (π ω) = π' (KaehlerDifferential.map A A' B B' ω))
variable (conn : Connection (π.compDer (KaehlerDifferential.D A B)) M)
variable (hconn : IsIntegrable conn C)

/-- The image of a horizontal scalar acts on the de Rham complex of the scalar-extended
connection along compatible Kähler quotients. -/
noncomputable def baseChangeDeRhamScalar (a : B)
    (h_da : (π.compDer (KaehlerDifferential.D A B)) a = 0) :
    deRhamComplex
        (scalarExtension conn φ
          (compatibleCalculi_of_quotient
            π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare).derivation)
        C' (scalarExtension_isIntegrable
          π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn) ⟶
      deRhamComplex
        (scalarExtension conn φ
          (compatibleCalculi_of_quotient
            π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare).derivation)
        C' (scalarExtension_isIntegrable
          π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn) :=
  let compat := compatibleCalculi_of_quotient
    π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare
  deRhamScalar
    (scalarExtension_isIntegrable
      π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn)
    (algebraMap B B' a) ((compat.derivation a).symm.trans
      ((congrArg φ h_da).trans φ.map_zero))

/-- A normalized splitting of the target one-forms and a linear coefficient operator
satisfying the scalar and image conditions give a reverse comparison whose two composites
are homotopic to multiplication by the horizontal scalar. -/
theorem existsReverseComparisonHomotopy
    (a : B) (z : B') (partialZ : B' → B') (d₁ : B' → B' ⊗[B] Ω)
    (theta : B' →ₗ[B] B') (formDecomp : Ω' ≃ₗ[B'] (B' ⊗[B] Ω) × B')
    (h_da : (π.compDer (KaehlerDifferential.D A B)) a = 0)
    (h_first_summand : ∀ ω : Ω,
      formDecomp (φ ω) = (TensorProduct.mk B B' Ω (1 : B') ω, 0))
    (h_z_normalization : formDecomp ((π'.compDer (KaehlerDifferential.D A' B')) z) = (0, 1))
    (h_decomposition : ∀ f : B',
      formDecomp ((π'.compDer (KaehlerDifferential.D A' B')) f) = (d₁ f, partialZ f))
    (h_partial_theta : ∀ f : B', partialZ (theta f) = algebraMap B B' a * f)
    (h_universallyInjective :
      LinearMap.UniversallyInjective.{v, v, v, v} (Algebra.linearMap B B'))
    (h_factor : ∀ f : B', ∃ b : B,
      algebraMap B B' b = algebraMap B B' a * f - theta (partialZ f))
    (h_horizontal : ∀ f : B', ∃ ω : Ω,
      TensorProduct.mk B B' Ω (1 : B') ω =
        TensorProduct.map theta (LinearMap.id : Ω →ₗ[B] Ω) (d₁ f) - d₁ (theta f)) :
    ∃ e :
        deRhamComplex
            (scalarExtension conn φ
              (compatibleCalculi_of_quotient
                π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare).derivation)
            C' (scalarExtension_isIntegrable
              π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn) ⟶
          deRhamComplex conn C hconn,
      Nonempty (Homotopy
        (baseChangeDeRhamHom
          π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn ≫ e)
        (deRhamScalar hconn a h_da)) ∧
      Nonempty (Homotopy
        (e ≫ baseChangeDeRhamHom
          π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn)
        (baseChangeDeRhamScalar
          π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn a h_da)) := sorry

end Connection
