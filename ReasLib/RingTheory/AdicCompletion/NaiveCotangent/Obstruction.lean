/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent
public import ReasLib.RingTheory.AdicCompletion.Polynomial.Evaluation

/-!
# Obstructions to lifting adic algebra maps
-/

@[expose] public section

noncomputable section

universe u

open Algebra.Extension

namespace Algebra.NaiveCotangent.Adic

variable {A B ι : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The quotient of the extended ideal power `I^n C` by its square `I^{2n} C`. -/
abbrev adicPowQuotient (I : Ideal A) (C : Type u) [CommRing C] [Algebra A C] (n : ℕ) :
    Type u :=
  (I.map (algebraMap A C) ^ n).Cotangent

/-- The coefficient module `I^n C / I^{2n} C` with scalars restricted along the
supplied residue algebra map from `B` to `C / I^n C`. -/
def coefficientModule (I : Ideal A) {C : Type u} [CommRing C] [Algebra A C] {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) : ModuleCat B :=
  (ModuleCat.restrictScalars ψn.toRingHom).obj
    (ModuleCat.of (C ⧸ I.map (algebraMap A C) ^ n) (adicPowQuotient I C n))

/-- Scalar multiplication on the coefficient module is the quotient action
through the supplied residue algebra map. -/
theorem coefficientModule_smul (I : Ideal A) {C : Type u} [CommRing C] [Algebra A C]
    {n : ℕ} (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) (scalar : B) :
    (coefficientModule I ψn).smul scalar =
      (ModuleCat.of (C ⧸ I.map (algebraMap A C) ^ n)
        (adicPowQuotient I C n)).smul (ψn scalar) :=
  rfl

/-- The Hom-cokernel of precomposition with the Jacobian of a completed
polynomial presentation, modeling the first Ext group of its naive cotangent complex. -/
abbrev ext1 [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) (N : Type u)
    [AddCommGroup N] [Module B N] : Type u :=
  (P.toExtension.Cotangent →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N (jacobian P))

/-- The cokernel class of a linear map from the conormal module. -/
def ext1.mk [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) {N : Type u}
    [AddCommGroup N] [Module B N] (f : P.toExtension.Cotangent →ₗ[B] N) : ext1 P N :=
  Submodule.Quotient.mk f

/-- A conormal map has zero cokernel class exactly when it factors through
the completed Jacobian. -/
theorem ext1_eq_zero_iff [Fintype ι] {I : Ideal A} (P : Presentation A B I ι)
    {N : Type u} [AddCommGroup N] [Module B N] (f : P.toExtension.Cotangent →ₗ[B] N) :
    ext1.mk P f = 0 ↔ ∃ h : (ι → B) →ₗ[B] N, f = h.comp (jacobian P) :=
  sorry

variable {C : Type u} [CommRing C] [Algebra A C]

/-- A map from a completed polynomial presentation lifts a residue map when
its reduction agrees with that residue map composed with the presentation. -/
def IsLift {I : Ideal A} (P : Presentation A B I ι) {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n)
    (ψ : polynomialCompletion A I ι →ₐ[A] C) : Prop :=
  (Ideal.Quotient.mkₐ A (I.map (algebraMap A C) ^ n)).comp ψ = ψn.comp P.toAlgHom

/-- For a finitely generated coefficient ideal, every residue algebra map
admits a lift from its completed polynomial presentation into an adically complete algebra. -/
theorem exists_lift {I : Ideal A} (hI : I.FG)
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (P : Presentation A B I ι) {n : ℕ} (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) :
    ∃ ψ : polynomialCompletion A I ι →ₐ[A] C, IsLift P ψn ψ :=
  sorry

namespace IsLift

/-- A lift of a residue map sends each presentation relation into the
corresponding extended ideal power. -/
theorem mem_map_pow {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ)
    {g : polynomialCompletion A I ι} (hg : g ∈ P.ker) :
    ψ g ∈ I.map (algebraMap A C) ^ n :=
  sorry

/-- The presentation kernel lies in the inverse image of the extended ideal
power under a lift of the residue map. -/
theorem ker_le_comap {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    P.ker ≤ (I.map (algebraMap A C) ^ n).comap ψ :=
  sorry

end IsLift

/-- Relation evaluation induces a function from the conormal module to the
power-ideal quotient by passing to cotangent classes. -/
private def obstructionHomValue {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ)
    (element : P.toExtension.Cotangent) : coefficientModule I ψn :=
  Ideal.mapCotangent P.ker (I.map (algebraMap A C) ^ n) ψ (IsLift.ker_le_comap hψ)
    (Cotangent.val element)

/-- Relation evaluation on conormal classes preserves addition. -/
private theorem obstructionHomValue_add {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ)
    (first second : P.toExtension.Cotangent) :
    obstructionHomValue hψ (first + second) =
      obstructionHomValue hψ first + obstructionHomValue hψ second :=
  sorry

/-- Relation evaluation is linear for the action of `B` through the residue map. -/
private theorem obstructionHomValue_smul {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ)
    (scalar : B) (element : P.toExtension.Cotangent) :
    obstructionHomValue hψ (scalar • element) = scalar • obstructionHomValue hψ element :=
  sorry

/-- The linear obstruction map sends a presentation relation to the class
of its value under the chosen lift. -/
@[no_expose] def obstructionHom {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    P.toExtension.Cotangent →ₗ[B] coefficientModule I ψn where
  toFun := obstructionHomValue hψ
  map_add' := obstructionHomValue_add hψ
  map_smul' := obstructionHomValue_smul hψ

/-- On the conormal class of a relation, the obstruction map is its evaluated
residue in the power-ideal quotient. -/
theorem obstructionHom_apply {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ)
    {g : polynomialCompletion A I ι} (hg : g ∈ P.ker) :
    obstructionHom hψ (Cotangent.mk ⟨g, hg⟩) =
      Ideal.toCotangent (I.map (algebraMap A C) ^ n) ⟨ψ g, IsLift.mem_map_pow hψ hg⟩ :=
  sorry

/-- The obstruction class is the cokernel class of relation evaluation
modulo precomposition with the completed Jacobian. -/
def obstructionClass [Fintype ι] {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    ext1 P (coefficientModule I ψn) :=
  ext1.mk P (obstructionHom hψ)

/-- The obstruction class vanishes exactly when relation evaluation factors
through the completed Jacobian with coefficients acted on through the residue map. -/
theorem obstructionClass_eq_zero_iff [Fintype ι] {I : Ideal A} {P : Presentation A B I ι}
    {n : ℕ} {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    obstructionClass hψ = 0 ↔
      ∃ h : (ι → B) →ₗ[B] coefficientModule I ψn,
        obstructionHom hψ = h.comp (jacobian P) :=
  sorry

/-- Inclusion of ideal powers induces a linear map between their cotangent quotients. -/
def map_adicPowQuotient (I : Ideal A) {n n' : ℕ} (h : n' ≤ n) :
    adicPowQuotient I C n →ₗ[C] adicPowQuotient I C n' :=
  Ideal.mapCotangent (I.map (algebraMap A C) ^ n) (I.map (algebraMap A C) ^ n')
    (AlgHom.id C C) fun _ hx ↦ Ideal.pow_le_pow_right h hx

/-- The coefficient transition sends the residue of an element to the residue
of the same element in the lower power-ideal quotient. -/
theorem map_adicPowQuotient_apply (I : Ideal A) {n n' : ℕ} (h : n' ≤ n) {x : C}
    (hx : x ∈ I.map (algebraMap A C) ^ n) :
    map_adicPowQuotient I h (Ideal.toCotangent (I.map (algebraMap A C) ^ n) ⟨x, hx⟩) =
      Ideal.toCotangent (I.map (algebraMap A C) ^ n') ⟨x, Ideal.pow_le_pow_right h hx⟩ :=
  sorry

/-- Coefficient transition after relation evaluation defines the reduced
obstruction function. -/
private def map_obstructionHomValue {I : Ideal A} {P : Presentation A B I ι} {n n' : ℕ}
    (h : n' ≤ n) {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ)
    (element : P.toExtension.Cotangent) :
    coefficientModule I ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)).comp ψn) :=
  map_adicPowQuotient I h (obstructionHom hψ element)

/-- Coefficient transition of relation evaluation preserves addition. -/
private theorem map_obstructionHomValue_add {I : Ideal A} {P : Presentation A B I ι}
    {n n' : ℕ} (h : n' ≤ n) {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ)
    (first second : P.toExtension.Cotangent) :
    map_obstructionHomValue h hψ (first + second) =
      map_obstructionHomValue h hψ first + map_obstructionHomValue h hψ second :=
  sorry

/-- Coefficient transition of relation evaluation is linear for the action of
`B` through the reduced residue map. -/
private theorem map_obstructionHomValue_smul {I : Ideal A} {P : Presentation A B I ι}
    {n n' : ℕ} (h : n' ≤ n) {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ)
    (scalar : B) (element : P.toExtension.Cotangent) :
    map_obstructionHomValue h hψ (scalar • element) =
      scalar • map_obstructionHomValue h hψ element :=
  sorry

/-- The coefficient-changed obstruction map uses the action of `B` through
the reduced residue algebra map. -/
@[no_expose] def map_obstructionHom [Fintype ι] {I : Ideal A} {P : Presentation A B I ι} {n n' : ℕ}
    (h : n' ≤ n) {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    P.toExtension.Cotangent →ₗ[B]
      coefficientModule I ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)).comp ψn) where
  toFun := map_obstructionHomValue h hψ
  map_add' := map_obstructionHomValue_add h hψ
  map_smul' := map_obstructionHomValue_smul h hψ

/-- Evaluation of the coefficient-changed obstruction map is coefficient
transition after the original obstruction map. -/
theorem map_obstructionHom_apply [Fintype ι] {I : Ideal A} {P : Presentation A B I ι}
    {n n' : ℕ} (h : n' ≤ n) {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ)
    (x : P.toExtension.Cotangent) :
    map_obstructionHom h hψ x = map_adicPowQuotient I h (obstructionHom hψ x) :=
  sorry

/-- The coefficient-changed obstruction class is the cokernel class of the
reduced relation-evaluation map. -/
def map_obstructionClass [Fintype ι] {I : Ideal A} {P : Presentation A B I ι} {n n' : ℕ}
    (h : n' ≤ n) {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    ext1 P
      (coefficientModule I ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)).comp ψn)) :=
  ext1.mk P (map_obstructionHom h hψ)

end Algebra.NaiveCotangent.Adic
