module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection.QuotientBaseChange
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct
open CategoryTheory

universe u v

section

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {A' : Type u} [CommRing A'] {B' : Type v} [CommRing B']
variable [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
variable [IsScalarTower A B B'] [IsScalarTower A A' B']
variable [SMulCommClass A' B B']
variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
variable {Ω' : Type v} [AddCommGroup Ω'] [Module B' Ω'] [Module A' Ω']
variable [IsScalarTower A' B' Ω'] [Module B Ω'] [IsScalarTower B B' Ω']
variable {M : Type v} [AddCommGroup M] [Module B M]

/- Remark 60.6.9 (1): compatible quotient maps transport a connection by
scalar extension. -/
@[stacks 07KJ] #check (Connection.baseChangeOfQuotient :
  ∀ (π : Ω[B⁄A] →ₗ[B] Ω) (π' : Ω[B'⁄A'] →ₗ[B'] Ω') (φ : Ω →ₗ[B] Ω'),
    (π'.restrictScalars B ∘ₗ KaehlerDifferential.map A A' B B' =
      φ.restrictScalars B ∘ₗ π) →
    Connection (π.compDer (KaehlerDifferential.D A B)) M →
    Connection (π'.compDer (KaehlerDifferential.D A' B')) (M ⊗[B] B'))

/- Remark 60.6.9 (2): scalar extension preserves integrability for compatible
quotient differential calculi. -/
@[stacks 07KJ] #check (Connection.scalarExtension_isIntegrable :
  ∀ (π : Ω[B⁄A] →ₗ[B] Ω) (hπ : Function.Surjective π)
    (δ : DifferentialOperator.DeRham.Family A B Ω[B⁄A])
    (hδ : DifferentialOperator.DeRham.IsDifferential
      (KaehlerDifferential.D A B) δ)
    (hcondition : DifferentialOperator.DeRham.KernelCondition π δ)
    (π' : Ω[B'⁄A'] →ₗ[B'] Ω') (hπ' : Function.Surjective π')
    (δ' : DifferentialOperator.DeRham.Family A' B' Ω[B'⁄A'])
    (hδ' : DifferentialOperator.DeRham.IsDifferential
      (KaehlerDifferential.D A' B') δ')
    (hcondition' : DifferentialOperator.DeRham.KernelCondition π' δ')
    (C : ExteriorCalculus (π.compDer (KaehlerDifferential.D A B))
      (KaehlerDifferential.DeRham.descendedFamily π hπ δ hδ hcondition))
    (C' : ExteriorCalculus (π'.compDer (KaehlerDifferential.D A' B'))
      (KaehlerDifferential.DeRham.descendedFamily π' hπ' δ' hδ' hcondition'))
    (φ : Ω →ₗ[B] Ω')
    (hsquare : ∀ ω, φ (π ω) = π' (KaehlerDifferential.map A A' B B' ω))
    (conn : Connection (π.compDer (KaehlerDifferential.D A B)) M)
    (hconn : Connection.IsIntegrable conn C),
    Connection.IsIntegrable
      (Connection.scalarExtension conn φ
        (Connection.compatibleCalculi_of_quotient
          π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare).derivation)
      C')

/- Remark 60.6.9 (3): the canonical map of de Rham complexes sends
`m ⊗ η` to `m ⊗ φ(η)`. -/
@[stacks 07KJ] #check (Connection.baseChangeDeRhamHom :
  ∀ (π : Ω[B⁄A] →ₗ[B] Ω) (hπ : Function.Surjective π)
    (δ : DifferentialOperator.DeRham.Family A B Ω[B⁄A])
    (hδ : DifferentialOperator.DeRham.IsDifferential
      (KaehlerDifferential.D A B) δ)
    (hcondition : DifferentialOperator.DeRham.KernelCondition π δ)
    (π' : Ω[B'⁄A'] →ₗ[B'] Ω') (hπ' : Function.Surjective π')
    (δ' : DifferentialOperator.DeRham.Family A' B' Ω[B'⁄A'])
    (hδ' : DifferentialOperator.DeRham.IsDifferential
      (KaehlerDifferential.D A' B') δ')
    (hcondition' : DifferentialOperator.DeRham.KernelCondition π' δ')
    (C : ExteriorCalculus (π.compDer (KaehlerDifferential.D A B))
      (KaehlerDifferential.DeRham.descendedFamily π hπ δ hδ hcondition))
    (C' : ExteriorCalculus (π'.compDer (KaehlerDifferential.D A' B'))
      (KaehlerDifferential.DeRham.descendedFamily π' hπ' δ' hδ' hcondition'))
    (φ : Ω →ₗ[B] Ω')
    (hsquare : ∀ ω, φ (π ω) = π' (KaehlerDifferential.map A A' B B' ω))
    (conn : Connection (π.compDer (KaehlerDifferential.D A B)) M)
    (hconn : Connection.IsIntegrable conn C),
    Connection.deRhamComplex conn C hconn ⟶
      Connection.deRhamComplex
        (Connection.scalarExtension conn φ
          (Connection.compatibleCalculi_of_quotient
            π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare).derivation)
        C'
        (Connection.scalarExtension_isIntegrable
          π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn))

#check Connection.scalarExtension_apply_tmul
#check Connection.baseChangeDeRhamHom_zero
#check Connection.baseChangeDeRhamHom_tmul

end
