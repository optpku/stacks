/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection.BaseChange

@[expose] public section

open scoped TensorProduct
open CategoryTheory

universe u v

namespace Connection

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {A' : Type u} [CommRing A'] {B' : Type v} [CommRing B']
variable [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
variable [IsScalarTower A B B'] [IsScalarTower A A' B']
variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
variable {Ω' : Type v} [AddCommGroup Ω'] [Module B' Ω'] [Module A' Ω']
variable [IsScalarTower A' B' Ω'] [Module B Ω'] [IsScalarTower B B' Ω']
variable {M : Type v} [AddCommGroup M] [Module B M]
variable [SMulCommClass A' B B']

/-- The commutative square of quotient differentials intertwines the induced
derivations. -/
theorem quotientDerivation_compatible
    (π : Ω[B⁄A] →ₗ[B] Ω) (π' : Ω[B'⁄A'] →ₗ[B'] Ω')
    (φ : Ω →ₗ[B] Ω')
    (hφ : π'.restrictScalars B ∘ₗ KaehlerDifferential.map A A' B B' =
      φ.restrictScalars B ∘ₗ π) (b : B) :
    φ ((π.compDer (KaehlerDifferential.D A B)) b) =
      (π'.compDer (KaehlerDifferential.D A' B')) (algebraMap B B' b) := by
  have h := LinearMap.congr_fun hφ (KaehlerDifferential.D A B b)
  change φ (π (KaehlerDifferential.D A B b)) =
    π' (KaehlerDifferential.D A' B' (algebraMap B B' b))
  simpa using h.symm

/-- Compatible Kähler quotient maps transport a connection by scalar extension. -/
noncomputable def baseChangeOfQuotient
    (π : Ω[B⁄A] →ₗ[B] Ω) (π' : Ω[B'⁄A'] →ₗ[B'] Ω')
    (φ : Ω →ₗ[B] Ω')
    (hφ : π'.restrictScalars B ∘ₗ KaehlerDifferential.map A A' B B' =
      φ.restrictScalars B ∘ₗ π)
    (conn : Connection (π.compDer (KaehlerDifferential.D A B)) M) :
    Connection (π'.compDer (KaehlerDifferential.D A' B')) (M ⊗[B] B') :=
  scalarExtension conn φ (quotientDerivation_compatible π π' φ hφ)

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

include hsquare in
/-- A compatible square of surjective Kähler quotients induces compatible exterior calculi. -/
theorem compatibleCalculi_of_quotient : CompatibleCalculi φ C C' := sorry

variable (conn : Connection (π.compDer (KaehlerDifferential.D A B)) M)
variable (hconn : IsIntegrable conn C)

include hconn in
/-- Scalar extension along compatible Kähler quotients preserves integrability of connections. -/
theorem scalarExtension_isIntegrable :
    IsIntegrable (scalarExtension conn φ
      (compatibleCalculi_of_quotient π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare).derivation)
      C' := sorry

/-- Compatible Kähler quotients induce the canonical morphism of de Rham complexes of connections. -/
noncomputable def baseChangeDeRhamHom :
    deRhamComplex conn C hconn ⟶
      deRhamComplex (scalarExtension conn φ
        (compatibleCalculi_of_quotient π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare).derivation)
        C' (scalarExtension_isIntegrable π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn) :=
  let compat := compatibleCalculi_of_quotient π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare
  let hconn' := scalarExtension_isIntegrable π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn
  { f := baseChangeDeRhamHom_f conn C hconn (scalarExtension conn φ compat.derivation) C' hconn' φ
    comm' := fun first second _ ↦
      baseChangeDeRhamHom_comm conn C hconn C' φ compat hconn' first second }

/-- Each component of the quotient base-change morphism is the explicit degreewise tensor map. -/
theorem baseChangeDeRhamHom_apply (degree : ℕ) :
    (baseChangeDeRhamHom π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn).f degree =
      baseChangeDeRhamHom_f conn C hconn
        (scalarExtension conn φ
          (compatibleCalculi_of_quotient π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare).derivation)
        C' (scalarExtension_isIntegrable π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn)
        φ degree := rfl

/-- The degree-zero component of quotient base change is coefficient inclusion. -/
theorem baseChangeDeRhamHom_zero (m : M) :
    (baseChangeDeRhamHom π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn).f 0 m =
      m ⊗ₜ[B] (1 : B') := sorry

/-- After tensor cancellation the positive-degree components apply the induced exterior-form map. -/
theorem baseChangeDeRhamHom_tmul (p : ℕ) (m : M) (η : exteriorPower.form B Ω (p + 1)) :
    cancelBaseChange_form (p + 1)
      ((baseChangeDeRhamHom π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn).f
        (p + 1) (m ⊗ₜ[B] η)) = m ⊗ₜ[B] inducedForm φ (p + 1) η := sorry

end Connection
