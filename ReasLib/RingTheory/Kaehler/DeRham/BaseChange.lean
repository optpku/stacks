/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.DeRham.Equiv
public import ReasLib.LinearAlgebra.ExteriorPower.BaseChange
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Kaehler.DeRham
public import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Base Change of the de Rham Complex

The standard Kähler comparison transports exterior-form differential families
from `Ω[A' ⊗[A] B⁄A']` to `(A' ⊗[A] B) ⊗[B] Ω[B⁄A]`.  The right tensor-product
algebra is selected through its opt-in scope, keeping this owner free of a
second global algebra instance.

`baseChangeTermEquiv` compares the scalar extension of the original complex
with the complex of the base-changed algebra. Its generator formula and
differential compatibility refer to that same specified equivalence.

@stack 0H8Y
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right
open DifferentialOperator.DeRham

universe u

namespace KaehlerDifferential.DeRham

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A B]

/-- Reassociation of coefficients, sending `a' ⊗ x` to `(a' ⊗ 1) ⊗ x`.
Both directions use the canonical tensor commutators and cancellation map. -/
noncomputable def baseChangeTensorEquiv (p : ℕ) :
    A' ⊗[A] term A B p ≃ₗ[A'] (A' ⊗[A] B) ⊗[B] Form A B p := by
  let swap : (A' ⊗[A] B) ≃ₗ[B] B ⊗[A] A' :=
    { toFun := TensorProduct.comm A A' B
      invFun := (TensorProduct.comm A A' B).symm
      map_add' := (TensorProduct.comm A A' B).map_add
      map_smul' := by sorry
      left_inv := (TensorProduct.comm A A' B).left_inv
      right_inv := (TensorProduct.comm A A' B).right_inv }
  let comparison :=
    ((TensorProduct.congr swap (LinearEquiv.refl B (Form A B p))).restrictScalars A).trans
      (((TensorProduct.comm B (B ⊗[A] A') (Form A B p)).restrictScalars A).trans
        (((TensorProduct.AlgebraTensorModule.cancelBaseChange A B B
          (Form A B p) A').restrictScalars A).trans
            (TensorProduct.comm A (Form A B p) A')))
  let source : term A B p ≃ₗ[A] Form A B p :=
    { toFun := fun form ↦ form
      invFun := fun form ↦ form
      map_add' := by intros; rfl
      map_smul' := by sorry
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let combined := ((source.baseChange A A').restrictScalars A).trans comparison.symm
  exact
    { toFun := combined
      invFun := combined.symm
      map_add' := combined.map_add
      map_smul' := by sorry
      left_inv := combined.left_inv
      right_inv := combined.right_inv }

/-- The coefficient reassociation on pure tensors. -/
theorem baseChangeTensorEquiv_tmul (p : ℕ) (scalar : A') (form : term A B p) :
    baseChangeTensorEquiv (A := A) (A' := A') (B := B) p (scalar ⊗ₜ[A] form) =
      (scalar ⊗ₜ[A] (1 : B)) ⊗ₜ[B] (form : Form A B p) := by
  rfl

/-- The canonical degreewise comparison for de Rham base change.
The exterior-power comparison uses explicit maps in both directions. -/
@[stacks 0H8Y]
noncomputable def baseChangeTermEquiv (p : ℕ) :
    A' ⊗[A] term A B p ≃ₗ[A'] term A' (A' ⊗[A] B) p := by
  let forms : (A' ⊗[A] B) ⊗[B] Form A B p ≃ₗ[A'] Form A' (A' ⊗[A] B) p :=
    (((((exteriorPowerEquiv A B p).baseChange B (A' ⊗[A] B)).trans
      (exteriorPower.baseChangeEquiv B (A' ⊗[A] B) Ω[B⁄A] p)).trans
        (exteriorPower.mapEquiv p
          (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)))).trans
            (exteriorPowerEquiv A' (A' ⊗[A] B) p).symm).restrictScalars A'
  let target : Form A' (A' ⊗[A] B) p ≃ₗ[A'] term A' (A' ⊗[A] B) p :=
    { toFun := fun form ↦ form
      invFun := fun form ↦ form
      map_add' := by intros; rfl
      map_smul' := by sorry
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact (baseChangeTensorEquiv (A := A) (A' := A') (B := B) p).trans (forms.trans target)

/-- The comparison agrees with the canonical map on basic differential forms. -/
@[stacks 0H8Y]
theorem baseChangeTermEquiv_basic (p : ℕ) (scalar : A') (coefficient : B)
    (entries : Fin p → B) :
    baseChangeTermEquiv (A := A) (A' := A') (B := B) p
        (scalar ⊗ₜ[A] basic A B p coefficient entries) =
      scalar • basic A' (A' ⊗[A] B) p (1 ⊗ₜ[A] coefficient)
        (fun index ↦ 1 ⊗ₜ[A] entries index) := by
  sorry

/-- The same degreewise comparison intertwines the original base-changed
differential with the differential of the base-changed algebra. -/
@[stacks 0H8Y]
theorem baseChangeTermEquiv_d (p : ℕ) :
    (baseChangeTermEquiv (A := A) (A' := A') (B := B) (p + 1)).toLinearMap.comp
        ((d A B p).hom.baseChange A') =
      (d A' (A' ⊗[A] B) p).hom.comp
        (baseChangeTermEquiv (A := A) (A' := A') (B := B) p).toLinearMap := by
  sorry

/-- The canonical de Rham base-change comparison in every degree, together
with its differential compatibility and its characterization on generators. -/
@[stacks 0H8Y]
theorem exists_complex_baseChange (A A' B : Type u)
    [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B] :
    ∃ equiv : ∀ p : ℕ,
        A' ⊗[A] term A B p ≃ₗ[A'] term A' (A' ⊗[A] B) p,
      (∀ p : ℕ,
        (equiv (p + 1)).toLinearMap.comp ((d A B p).hom.baseChange A') =
          (d A' (A' ⊗[A] B) p).hom.comp (equiv p).toLinearMap) ∧
      (∀ (p : ℕ) (scalar : A') (coefficient : B) (entries : Fin p → B),
        equiv p (scalar ⊗ₜ[A] basic A B p coefficient entries) =
          scalar • basic A' (A' ⊗[A] B) p (1 ⊗ₜ[A] coefficient)
            (fun index ↦ 1 ⊗ₜ[A] entries index)) := by
  refine ⟨fun p ↦ baseChangeTermEquiv (A := A) (A' := A') (B := B) p, ?_, ?_⟩
  · exact fun p ↦ baseChangeTermEquiv_d p
  · exact fun p scalar coefficient entries ↦ baseChangeTermEquiv_basic p scalar coefficient entries

/-- The universal derivation after transport through the Kähler base-change
comparison. -/
@[stacks 0H8Y]
noncomputable def baseChangeDerivation :
    Derivation A' (A' ⊗[A] B) ((A' ⊗[A] B) ⊗[B] Ω[B⁄A]) :=
  (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).symm.toLinearMap.compDer
    (KaehlerDifferential.D A' (A' ⊗[A] B))

/-- Transport a differential family through the Kähler base-change
comparison. -/
@[stacks 0H8Y]
noncomputable def baseChange
    (δ : Family A' (A' ⊗[A] B) Ω[A' ⊗[A] B⁄A']) :
    Family A' (A' ⊗[A] B) ((A' ⊗[A] B) ⊗[B] Ω[B⁄A]) :=
  Family.transport
    (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).symm δ

/-- The Kähler base-change comparison intertwines a differential family with
its transport. -/
@[stacks 0H8Y]
theorem baseChange_descends
    (δ : Family A' (A' ⊗[A] B) Ω[A' ⊗[A] B⁄A']) :
    Descends (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).toLinearMap
      (baseChange δ) δ := by
  simpa [baseChange] using
    Family.transport_descends_symm
      (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).symm δ

/-- Base change preserves the square-zero relation of a differential
family. -/
@[stacks 0H8Y]
theorem baseChange_squaresToZero
    (δ : Family A' (A' ⊗[A] B) Ω[A' ⊗[A] B⁄A'])
    (hδ : SquaresToZero δ) :
    SquaresToZero (baseChange δ) := by
  simpa [baseChange] using
    Family.transport_squaresToZero
      (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).symm δ hδ

/-- Base change transports the de Rham formulas for the universal
derivation. -/
@[stacks 0H8Y]
theorem baseChange_satisfiesFormula
    (δ : Family A' (A' ⊗[A] B) Ω[A' ⊗[A] B⁄A'])
    (hδ : SatisfiesFormula (KaehlerDifferential.D A' (A' ⊗[A] B)) δ) :
    SatisfiesFormula baseChangeDerivation (baseChange δ) := by
  simpa [baseChange, baseChangeDerivation] using
    Family.transport_satisfiesFormula
      (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).symm δ hδ

/-- The transported family is a de Rham differential family for the
transported derivation. -/
@[stacks 0H8Y]
theorem baseChange_isDifferential
    (δ : Family A' (A' ⊗[A] B) Ω[A' ⊗[A] B⁄A'])
    (hδ : IsDifferential (KaehlerDifferential.D A' (A' ⊗[A] B)) δ) :
    IsDifferential baseChangeDerivation (baseChange δ) := by
  simpa [baseChange, baseChangeDerivation] using
    Family.transport_isDifferential
      (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).symm δ hδ

end KaehlerDifferential.DeRham
