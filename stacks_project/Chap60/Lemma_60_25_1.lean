/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection.SplitBaseChange
public import stacks_project.Chap60.Lemma_60_25_1_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {A' : Type u} [CommRing A'] {B' : Type v} [CommRing B']
variable [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
variable [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
variable {Ω' : Type v} [AddCommGroup Ω'] [Module B' Ω'] [Module A' Ω']
variable [IsScalarTower A' B' Ω'] [Module B Ω'] [IsScalarTower B B' Ω']
variable {M : Type v} [AddCommGroup M] [Module B M]

/- Lemma 60.25.1: under the seven split de Rham base-change conditions, the
canonical comparison for an integrable connection has a reverse map whose two
composites are homotopic to multiplication by the horizontal scalar. -/
@[stacks 07Q7] #check (Connection.existsReverseComparisonHomotopy :
  ∀ (π : Ω[B⁄A] →ₗ[B] Ω) (hπ : Function.Surjective π)
    (δ : DifferentialOperator.DeRham.Family A B Ω[B⁄A])
    (hδ : DifferentialOperator.DeRham.IsDifferential (KaehlerDifferential.D A B) δ)
    (hcondition : DifferentialOperator.DeRham.KernelCondition π δ)
    (π' : Ω[B'⁄A'] →ₗ[B'] Ω') (hπ' : Function.Surjective π')
    (δ' : DifferentialOperator.DeRham.Family A' B' Ω[B'⁄A'])
    (hδ' : DifferentialOperator.DeRham.IsDifferential (KaehlerDifferential.D A' B') δ')
    (hcondition' : DifferentialOperator.DeRham.KernelCondition π' δ')
    (C : ExteriorCalculus (π.compDer (KaehlerDifferential.D A B))
      (KaehlerDifferential.DeRham.descendedFamily π hπ δ hδ hcondition))
    (C' : ExteriorCalculus (π'.compDer (KaehlerDifferential.D A' B'))
      (KaehlerDifferential.DeRham.descendedFamily π' hπ' δ' hδ' hcondition'))
    (φ : Ω →ₗ[B] Ω')
    (hsquare : ∀ ω, φ (π ω) = π' (KaehlerDifferential.map A A' B B' ω))
    (conn : Connection (π.compDer (KaehlerDifferential.D A B)) M)
    (hconn : Connection.IsIntegrable conn C)
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
        TensorProduct.map theta (LinearMap.id : Ω →ₗ[B] Ω) (d₁ f) - d₁ (theta f)),
    ∃ e :
        Connection.deRhamComplex
            (Connection.scalarExtension conn φ
              (Connection.compatibleCalculi_of_quotient
                π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare).derivation)
            C' (Connection.scalarExtension_isIntegrable
              π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn) ⟶
          Connection.deRhamComplex conn C hconn,
      Nonempty (Homotopy
        (Connection.baseChangeDeRhamHom
          π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn ≫ e)
        (Connection.deRhamScalar hconn a h_da)) ∧
      Nonempty (Homotopy
        (e ≫ Connection.baseChangeDeRhamHom
          π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn)
        (Connection.baseChangeDeRhamScalar
          π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn a h_da)))
