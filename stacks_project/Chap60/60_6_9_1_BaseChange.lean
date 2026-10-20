/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection.BaseChange

@[expose] public section

open scoped TensorProduct

universe u v

section

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
variable {A' : Type u} [CommRing A'] {B' : Type v} [CommRing B']
variable [Algebra A' B'] [Algebra B B']
variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
variable {Ω' : Type v} [AddCommGroup Ω'] [Module B' Ω'] [Module A' Ω']
variable [IsScalarTower A' B' Ω'] [Module B Ω'] [IsScalarTower B B' Ω']
variable {M : Type v} [AddCommGroup M] [Module B M]
variable {D : Derivation A B Ω} {δ : DifferentialOperator.DeRham.Family A B Ω}
variable {D' : Derivation A' B' Ω'} {δ' : DifferentialOperator.DeRham.Family A' B' Ω'}

/- The coefficient inclusion used by scalar-extension connections. -/
#check (Connection.coeffInclude : M →ₗ[B] M ⊗[B] B')

/- The tensor cancellation identifying the target form terms with restricted form tensors. -/
#check (Connection.cancelBaseChange_form : ∀ p : ℕ,
  (M ⊗[B] B') ⊗[B'] exteriorPower.form B' Ω' p ≃ₗ[B] M ⊗[B] exteriorPower.form B' Ω' p)

/- Compatibility of derivations, exterior differentials, and wedge operations. -/
#check (Connection.CompatibleCalculi : (Ω →ₗ[B] Ω') →
  ExteriorCalculus D δ → ExteriorCalculus D' δ' → Prop)

end
