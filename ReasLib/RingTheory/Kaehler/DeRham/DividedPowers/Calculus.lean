/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers
public import ReasLib.LinearAlgebra.ExteriorPower.Wedge
public import ReasLib.RingTheory.DividedPowers.Polynomial
public import ReasLib.RingTheory.Kaehler.DeRham.Connection

public section

open CategoryTheory
open exteriorPower.form
open scoped TensorProduct

universe u

namespace DPPolynomial.DeRham

/-- Ambient algebra `A → P` through `B → P`. -/
@[expose]
noncomputable instance (priority := 1000) algebraA_polyOver
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] {ι : Type u} :
    Algebra A (DPPolynomial B ι) :=
  ((algebraMap B (DPPolynomial B ι)).comp (algebraMap A B)).toAlgebra

/-- The tower `A → B → P`. -/
@[expose]
instance (priority := 1000) isScalarTower_polyOver
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] {ι : Type u} :
    IsScalarTower A B (DPPolynomial B ι) :=
  sorry

/-- Divided-power relations in `Ω[B⁄A]`. -/
@[expose]
noncomputable def relationsB (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) : Submodule B Ω[B⁄A] :=
  KaehlerDifferential.DeRham.ambientDividedPowerRelations (A := A) δ

/-- Divided-power relations in `Ω[P⁄A]`. -/
@[expose]
noncomputable def relationsP (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) (ι : Type u) :
    Submodule (DPPolynomial B ι) Ω[DPPolynomial B ι ⁄ A] :=
  KaehlerDifferential.DeRham.ambientDividedPowerRelations (A := A)
    (DPPolynomial.dividedPowers (ι := ι) δ)

/-- Relative divided-power one-forms `Ω_{B/A,δ}`. -/
@[expose]
abbrev formB (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) : Type u :=
  KaehlerDifferential.DeRham.ambientDividedPowerDifferential (A := A) δ

/-- Relative divided-power one-forms `Ω_{P/A,δ}` for `P = B⟨x_i⟩`. -/
@[expose]
abbrev formP (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) (ι : Type u) : Type u :=
  KaehlerDifferential.DeRham.ambientDividedPowerDifferential (A := A)
    (DPPolynomial.dividedPowers (ι := ι) δ)

/-- Restrict scalars of `Ω[P⁄A]` along `B → P`. -/
@[expose]
noncomputable instance moduleB_kaehlerP (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (ι : Type u) : Module B Ω[DPPolynomial B ι ⁄ A] :=
  Module.compHom _ (algebraMap B (DPPolynomial B ι))

/-- Restrict scalars of `Ω_{P/A,δ}` along `B → P`. -/
@[expose]
noncomputable instance moduleB_formP (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) {ι : Type u} :
    Module B (formP A B δ ι) :=
  Module.compHom _ (algebraMap B (DPPolynomial B ι))

/-- Restrict scalars of `Ω_{P/A,δ}` along `A → P`. -/
@[expose]
noncomputable instance moduleA_formP (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) {ι : Type u} :
    Module A (formP A B δ ι) :=
  Module.compHom _ (algebraMap A (DPPolynomial B ι))

/-- Restrict scalars of `Ω[P⁄A]` along `A → P`. -/
@[expose]
noncomputable instance moduleA_kaehlerP (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (ι : Type u) : Module A Ω[DPPolynomial B ι ⁄ A] :=
  Module.compHom _ (algebraMap A (DPPolynomial B ι))

/-- The tower `A → B → Ω_{P/A,δ}`. -/
@[expose]
instance isScalarTower_formP (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) {ι : Type u} :
    IsScalarTower A B (formP A B δ ι) :=
  sorry

/-- The tower `A → P → Ω_{P/A,δ}`. -/
@[expose]
instance (priority := 1000) isScalarTower_A_poly_formP
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) {ι : Type u} :
    IsScalarTower A (DPPolynomial B ι) (formP A B δ ι) :=
  sorry

/-- The tower `A → P → Ω[P⁄A]`. -/
@[expose]
instance (priority := 1000) isScalarTower_A_poly_kaehlerP
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] {ι : Type u} :
    IsScalarTower A (DPPolynomial B ι) Ω[DPPolynomial B ι ⁄ A] :=
  sorry

/-- The tower `B → P → Ω_{P/A,δ}`. -/
@[expose]
instance isScalarTower_B_poly_formP (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) {ι : Type u} :
    IsScalarTower B (DPPolynomial B ι) (formP A B δ ι) :=
  sorry

/-- Compatibility of the `B` and `P` actions on `Ω[P⁄A]` and its quotient. -/
@[expose]
instance compatibleSMul_relationsP (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) {ι : Type u} :
    LinearMap.CompatibleSMul Ω[DPPolynomial B ι ⁄ A] (formP A B δ ι) B (DPPolynomial B ι) :=
  sorry

/-- The universal divided-power derivation of `B` over `A`. -/
@[expose]
noncomputable def derivationB (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) :
    Derivation A B (formB A B δ) :=
  KaehlerDifferential.DeRham.ambientDividedPowerDifferentialDerivation (A := A) δ

/-- The universal divided-power derivation of `P` over `A`, viewed as a `B`-derivation. -/
@[expose]
noncomputable def derivationP (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) (ι : Type u) :
    Derivation A B (formP A B δ ι) :=
  Derivation.mk'
    { toFun := fun b ↦
        (relationsP A B δ ι).mkQ
          (KaehlerDifferential.D A (DPPolynomial B ι) (algebraMap B (DPPolynomial B ι) b))
      map_add' := sorry
      map_smul' := sorry }
    sorry

/-- The `B`-linear comparison of one-forms induced by `algebraMap B P`. -/
@[expose]
noncomputable def formMap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) (ι : Type u) :
    formB A B δ →ₗ[B] formP A B δ ι :=
  Submodule.liftQ (relationsB A B δ)
    (Derivation.liftKaehlerDifferential (derivationP A B δ ι))
    sorry

section Calculus

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)

/-- The canonical restricted scalar action on exterior-form terms. -/
@[expose]
instance formScalarModule {Ω : Type u} [AddCommGroup Ω] [Module B Ω]
    [Module A Ω] [IsScalarTower A B Ω] (degree : ℕ) :
    Module A (exteriorPower.form B Ω degree) :=
  exteriorPower.form.moduleOfScalarTower degree

/-- The restricted action agrees with the coefficient action. -/
@[expose]
instance formScalarTower {Ω : Type u} [AddCommGroup Ω] [Module B Ω]
    [Module A Ω] [IsScalarTower A B Ω] (degree : ℕ) :
    IsScalarTower A B (exteriorPower.form B Ω degree) :=
  exteriorPower.form.isScalarTower_moduleOfScalarTower degree

/-- Evaluation of basic divided-power forms in the canonical exterior powers. -/
@[expose]
noncomputable def basicEvaluation (degree : ℕ) :
    ((B × (Fin degree → B)) →₀ B) →ₗ[A]
      exteriorPower.form B (formB A B δ) degree :=
  (Finsupp.linearCombination B (fun entries ↦
    DifferentialOperator.DeRham.basicForm (derivationB A B δ) degree
      entries.1 entries.2)).restrictScalars A

/-- The universal divided-power derivation generates every exterior-form term. -/
theorem basicEvaluation_surjective (degree : ℕ) :
    Function.Surjective (basicEvaluation (A := A) (B := B) (δ := δ) degree) := sorry

/-- The basic-form differential differentiates the coefficient and appends its differential. -/
@[expose]
noncomputable def basicDifferential (degree : ℕ) :
    ((B × (Fin degree → B)) →₀ B) →ₗ[A]
      exteriorPower.form B (formB A B δ) (degree + 1) :=
  Finsupp.lsum A (fun entries ↦
    { toFun := fun coefficient ↦ DifferentialOperator.DeRham.exactForm
        (derivationB A B δ) (degree + 1) (Fin.cons (coefficient * entries.1) entries.2)
      map_add' := sorry
      map_smul' := sorry })

/-- On a formal generator the basic differential differentiates its full coefficient. -/
theorem basicDifferential_single (degree : ℕ) (coefficient scalar : B)
    (entries : Fin degree → B) :
    basicDifferential A B δ degree (Finsupp.single (coefficient, entries) scalar) =
      DifferentialOperator.DeRham.exactForm (derivationB A B δ) (degree + 1)
        (Fin.cons (scalar * coefficient) entries) := sorry

/-- Equal evaluations of formal basic forms have equal basic differentials. -/
theorem basicDifferential_eq_of_evaluation_eq (degree : ℕ)
    (first second : (B × (Fin degree → B)) →₀ B)
    (h_eval : basicEvaluation A B δ degree first = basicEvaluation A B δ degree second) :
    basicDifferential A B δ degree first = basicDifferential A B δ degree second := sorry

/-- A total selector of formal basic-form representatives, independent of generation proofs. -/
private noncomputable def basicRepresentative (degree : ℕ) :
    exteriorPower.form B (formB A B δ) degree → ((B × (Fin degree → B)) →₀ B) :=
  Function.invFun (basicEvaluation A B δ degree)

/-- The canonical divided-power de Rham differential, descended from basic generators. -/
noncomputable def canonicalFamily :
    DifferentialOperator.DeRham.Family A B (formB A B δ) :=
  fun degree ↦
    { toFun := fun form ↦ basicDifferential A B δ degree
        (basicRepresentative A B δ degree form)
      map_add' := sorry
      map_smul' := sorry }

/-- The canonical differential factors the basic differential through evaluation. -/
theorem canonicalFamily_comp_basicEvaluation (degree : ℕ) :
    (canonicalFamily A B δ degree).comp (basicEvaluation A B δ degree) =
      basicDifferential A B δ degree := sorry

/-- The canonical family has the defining divided-power de Rham formula. -/
theorem canonicalFamily_basic (degree : ℕ) (coefficient : B) (entries : Fin degree → B) :
    canonicalFamily A B δ degree
        (DifferentialOperator.DeRham.basicForm (derivationB A B δ) degree
          coefficient entries) =
      DifferentialOperator.DeRham.exactForm (derivationB A B δ) (degree + 1)
        (Fin.cons coefficient entries) := sorry

/-- The differential factoring the basic differential through evaluation is unique. -/
theorem canonicalFamily_unique
    (family : DifferentialOperator.DeRham.Family A B (formB A B δ))
    (h_factor : ∀ degree, (family degree).comp (basicEvaluation A B δ degree) =
      basicDifferential A B δ degree) : family = canonicalFamily A B δ := sorry

/-- The canonical divided-power exterior calculus. -/
@[expose]
noncomputable def canonicalCalculus :
    ExteriorCalculus (derivationB A B δ) (canonicalFamily A B δ) :=
  { leftWedge := wedge B 1
    leftWedgeTwo := wedge B 2
    differential_smul := sorry
    differential_leftWedge := sorry
    leftWedge_assoc := sorry
    isDifferential := sorry }

/-- The canonical calculus uses the usual exterior multiplication. -/
theorem canonicalCalculus_leftWedge (degree : ℕ) :
    (canonicalCalculus A B δ).leftWedge degree = wedge B 1 degree := sorry

end Calculus

end DPPolynomial.DeRham

end
