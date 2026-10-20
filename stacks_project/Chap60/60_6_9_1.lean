/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Kaehler.DeRham.Connection.QuotientBaseChange

@[expose] public section

open scoped TensorProduct
open CategoryTheory

universe u v

section

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {A' : Type u} [CommRing A'] {B' : Type v} [CommRing B']
variable [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
variable [IsScalarTower A B B'] [IsScalarTower A A' B']
variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
variable {Ω' : Type v} [AddCommGroup Ω'] [Module B' Ω'] [Module A' Ω']
variable [IsScalarTower A' B' Ω'] [Module B Ω'] [IsScalarTower B B' Ω']
variable {M : Type v} [AddCommGroup M] [Module B M]

/- 60.6.9.1: a commutative ring square with compatible surjective Kähler quotients
induces the canonical de Rham complex morphism of an integrable connection and
its scalar extension. In degree zero it sends m to m ⊗ₜ[B] 1; in positive degrees,
tensor cancellation identifies its value on m ⊗ₜ[B] η with
m ⊗ₜ[B] Connection.inducedForm φ (p + 1) η in degree p + 1. -/
@[stacks 07PY] #check (Connection.baseChangeDeRhamHom :
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
    (hconn : Connection.IsIntegrable conn C),
  Connection.deRhamComplex conn C hconn ⟶
    Connection.deRhamComplex (Connection.scalarExtension conn φ
      (Connection.compatibleCalculi_of_quotient
        π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare).derivation)
      C' (Connection.scalarExtension_isIntegrable
        π hπ δ hδ hcondition π' hπ' δ' hδ' hcondition' C C' φ hsquare conn hconn))

end
