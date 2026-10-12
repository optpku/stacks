/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import stacks_project.Chap88.«88_3_0_1_NaiveCotangent»

/-!
# Obstruction class of a lift of an adic algebra map

This leaf owns the coefficient module `I^n C / I^{2n} C`, the Hom-coker model of
`Ext¹_B(NL_{B/A}^∧, −)`, and the obstruction class of a chosen lift of
`ψn : B →ₐ[A] C ⧸ I^n C`.
-/

@[expose] public section

noncomputable section

universe u

open Algebra.Extension

namespace Algebra.NaiveCotangent.Adic

variable {A B ι : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The coefficient module `I^n C / I^{2n} C`, as the cotangent of the power
`(I.map (algebraMap A C))^n`. -/
abbrev adicPowQuotient (I : Ideal A) (C : Type u) [CommRing C] [Algebra A C] (n : ℕ) :
    Type u :=
  (I.map (algebraMap A C) ^ n).Cotangent

/-- The residue of an element of `I^n C` in `I^n C / I^{2n} C`. -/
def toAdicPowQuotient (I : Ideal A) (C : Type u) [CommRing C] [Algebra A C] (n : ℕ) :=
  Ideal.toCotangent (I.map (algebraMap A C) ^ n)

/-- The residue map `I^n C → I^n C / I^{2n} C` is `Ideal.toCotangent`. -/
theorem toAdicPowQuotient_eq (I : Ideal A) (C : Type u) [CommRing C] [Algebra A C] (n : ℕ) :
    toAdicPowQuotient I C n = Ideal.toCotangent (I.map (algebraMap A C) ^ n) :=
  sorry

/-- A residue in `I^n C / I^{2n} C` vanishes iff the representative lies in `I^{2n} C`. -/
theorem toAdicPowQuotient_eq_zero (I : Ideal A) (C : Type u) [CommRing C] [Algebra A C]
    (n : ℕ) {x : C} (hx : x ∈ I.map (algebraMap A C) ^ n) :
    toAdicPowQuotient I C n ⟨x, hx⟩ = 0 ↔ x ∈ I.map (algebraMap A C) ^ (2 * n) :=
  sorry

/-- The `B`-module structure on `I^n C / I^{2n} C` obtained by restricting the
canonical `C ⧸ I^n C`-action along `ψn`. -/
@[reducible]
def moduleOfAlgHom (I : Ideal A) {C : Type u} [CommRing C] [Algebra A C] {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) :
    Module B (adicPowQuotient I C n) :=
  Module.compHom (adicPowQuotient I C n) ψn.toRingHom

/-- Unfolding of `moduleOfAlgHom` as restriction of scalars along `ψn`. -/
theorem moduleOfAlgHom_eq (I : Ideal A) {C : Type u} [CommRing C] [Algebra A C] {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) :
    moduleOfAlgHom I ψn = Module.compHom (adicPowQuotient I C n) ψn.toRingHom :=
  sorry

/-- `B`-linear maps into `I^n C / I^{2n} C` with the `B`-action along `ψn`. -/
abbrev linearMapOfAlgHom (I : Ideal A) {C : Type u} [CommRing C] [Algebra A C] {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) (M : Type u)
    [AddCommGroup M] [Module B M] : Type u :=
  @LinearMap B B _ _ (RingHom.id B) M (adicPowQuotient I C n) _ _ _
    (moduleOfAlgHom I ψn)

/-- Unfolding of `linearMapOfAlgHom` as a `LinearMap` with the `B`-action along `ψn`. -/
theorem linearMapOfAlgHom_eq (I : Ideal A) {C : Type u} [CommRing C] [Algebra A C] {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) (M : Type u)
    [AddCommGroup M] [Module B M] :
    linearMapOfAlgHom I ψn M =
      @LinearMap B B _ _ (RingHom.id B) M (adicPowQuotient I C n) _ _ _
        (moduleOfAlgHom I ψn) :=
  sorry

/-- Package an underlying map as a `B`-linear map into `I^n C / I^{2n} C` along `ψn`. -/
def linearMapOfAlgHom.mk {I : Ideal A} {C : Type u} [CommRing C] [Algebra A C] {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) {M : Type u}
    [AddCommGroup M] [Module B M] (toFun : M → adicPowQuotient I C n) :
    linearMapOfAlgHom I ψn M :=
  @LinearMap.mk B B _ _ (RingHom.id B) M (adicPowQuotient I C n) _ _ _
    (moduleOfAlgHom I ψn) { toFun := toFun, map_add' := sorry } sorry

/-- `linearMapOfAlgHom.mk` evaluates as the packaged underlying function. -/
theorem linearMapOfAlgHom.mk_apply {I : Ideal A} {C : Type u} [CommRing C] [Algebra A C]
    {n : ℕ} (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) {M : Type u}
    [AddCommGroup M] [Module B M] (toFun : M → adicPowQuotient I C n) (x : M) :
    linearMapOfAlgHom.mk ψn toFun x = toFun x :=
  sorry

/-- Precomposition with the Jacobian of a completed presentation. -/
def jacobianHom [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) (N : Type u)
    [AddCommGroup N] [Module B N] :
    ((ι → B) →ₗ[B] N) →ₗ[B] (P.toExtension.Cotangent →ₗ[B] N) :=
  LinearMap.lcomp B N (jacobian P)

/-- Evaluating `jacobianHom` is precomposition with `jacobian P`. -/
theorem jacobianHom_apply [Fintype ι] {I : Ideal A} (P : Presentation A B I ι)
    (N : Type u) [AddCommGroup N] [Module B N] (h : (ι → B) →ₗ[B] N)
    (x : P.toExtension.Cotangent) :
    jacobianHom P N h x = h (jacobian P x) :=
  sorry

/-- The working model of `Ext¹_B(NL_{B/A}^∧, N)` as the cokernel of
`Hom_B(⊕ᵢ B dx_i, N) → Hom_B(J / J², N)`, the identification of More on Algebra
Lemma 15.85.4 (1) already used by `Algebra.annihilatesExt1NaiveCotangent`. -/
abbrev ext1 [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) (N : Type u)
    [AddCommGroup N] [Module B N] : Type u :=
  (P.toExtension.Cotangent →ₗ[B] N) ⧸ LinearMap.range (jacobianHom P N)

/-- The class of a `B`-linear map out of `J / J²` in the Hom-coker model of `Ext¹`. -/
def ext1.mk [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) {N : Type u}
    [AddCommGroup N] [Module B N] (f : P.toExtension.Cotangent →ₗ[B] N) : ext1 P N :=
  Submodule.Quotient.mk f

/-- Unfolding of `ext1.mk`. -/
theorem ext1.mk_eq [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) {N : Type u}
    [AddCommGroup N] [Module B N] (f : P.toExtension.Cotangent →ₗ[B] N) :
    ext1.mk P f = Submodule.Quotient.mk f :=
  sorry

/-- A class in the Hom-coker model of `Ext¹` vanishes iff the representative
factors through the Jacobian. -/
theorem ext1_eq_zero_iff [Fintype ι] {I : Ideal A} (P : Presentation A B I ι)
    {N : Type u} [AddCommGroup N] [Module B N] (f : P.toExtension.Cotangent →ₗ[B] N) :
    ext1.mk P f = 0 ↔ ∃ h : (ι → B) →ₗ[B] N, f = h.comp (jacobian P) :=
  sorry

variable {C : Type u} [CommRing C] [Algebra A C]

/-- Compatibility of a map `ψ : A[x_ι]^∧ →ₐ[A] C` with a residue map
`ψn : B →ₐ[A] C ⧸ I^n C` along a completed presentation. -/
def IsLift {I : Ideal A} (P : Presentation A B I ι) {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n)
    (ψ : polynomialCompletion A I ι →ₐ[A] C) : Prop :=
  (Ideal.Quotient.mkₐ A (I.map (algebraMap A C) ^ n)).comp ψ = ψn.comp P.toAlgHom

/-- Unfolding of `IsLift`. -/
theorem isLift_iff {I : Ideal A} (P : Presentation A B I ι) {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n)
    (ψ : polynomialCompletion A I ι →ₐ[A] C) :
    IsLift P ψn ψ ↔
      (Ideal.Quotient.mkₐ A (I.map (algebraMap A C) ^ n)).comp ψ = ψn.comp P.toAlgHom :=
  sorry

/-- A lift of `ψn` along `A[x_ι]^∧ → B` exists in an `I`-adically complete algebra by
lifting the residues of the images of the variables and applying completed evaluation.
No preferred lift is chosen as public data. -/
theorem exists_lift {I : Ideal A} [IsAdicComplete (I.map (algebraMap A C)) C]
    (P : Presentation A B I ι) {n : ℕ} (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) :
    ∃ ψ : polynomialCompletion A I ι →ₐ[A] C, IsLift P ψn ψ :=
  sorry

namespace IsLift

/-- A lift of `ψn` sends the presentation kernel into `I^n C`. -/
theorem mem_map_pow {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ)
    {g : polynomialCompletion A I ι} (hg : g ∈ P.ker) :
    ψ g ∈ I.map (algebraMap A C) ^ n :=
  sorry

/-- A lift of `ψn` sends the presentation kernel into the comap of `I^n C`. -/
theorem ker_le_comap {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    P.ker ≤ (I.map (algebraMap A C) ^ n).comap ψ :=
  sorry

end IsLift

/-- Precomposition with the Jacobian as maps into `I^n C / I^{2n} C` along `ψn`. -/
def jacobianHomOfAlgHom [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n)
    (h : linearMapOfAlgHom I ψn (ι → B)) :
    linearMapOfAlgHom I ψn P.toExtension.Cotangent :=
  @jacobianHom _ _ _ _ _ _ _ _ P (adicPowQuotient I C n) _ (moduleOfAlgHom I ψn) h

/-- Evaluating `jacobianHomOfAlgHom` is precomposition with `jacobian P`. -/
theorem jacobianHomOfAlgHom_apply [Fintype ι] {I : Ideal A} (P : Presentation A B I ι)
    {n : ℕ} (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n)
    (h : linearMapOfAlgHom I ψn (ι → B)) (x : P.toExtension.Cotangent) :
    jacobianHomOfAlgHom P ψn h x = h (jacobian P x) :=
  sorry

/-- Two maps into `I^n C / I^{2n} C` along `ψn` represent the same `Ext¹` class
when they differ by precomposition with the Jacobian. -/
def Ext1Rel [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n)
    (f g : linearMapOfAlgHom I ψn P.toExtension.Cotangent) : Prop :=
  ∃ h : linearMapOfAlgHom I ψn (ι → B),
    ∀ x, f x - g x = jacobianHomOfAlgHom P ψn h x

/-- Unfolding of the Hom-coker relation along `ψn`. -/
theorem Ext1Rel_iff [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n)
    (f g : linearMapOfAlgHom I ψn P.toExtension.Cotangent) :
    Ext1Rel P ψn f g ↔
      ∃ h : linearMapOfAlgHom I ψn (ι → B),
        ∀ x, f x - g x = jacobianHomOfAlgHom P ψn h x :=
  sorry

/-- The Hom-coker of `jacobianHom` with coefficients `I^n C / I^{2n} C` along `ψn`. -/
abbrev ext1OfAlgHom [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) : Type u :=
  Quot (Ext1Rel P ψn)

/-- Unfolding of `ext1OfAlgHom` as the Hom-coker quotient along `ψn`. -/
theorem ext1OfAlgHom_eq [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) :
    ext1OfAlgHom P ψn = Quot (Ext1Rel P ψn) :=
  sorry

/-- The class of a `B`-linear map into `I^n C / I^{2n} C` along `ψn`. -/
def ext1OfAlgHom.mk [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n)
    (f : linearMapOfAlgHom I ψn P.toExtension.Cotangent) : ext1OfAlgHom P ψn :=
  Quot.mk (Ext1Rel P ψn) f

/-- Unfolding of `ext1OfAlgHom.mk`. -/
theorem ext1OfAlgHom.mk_eq [Fintype ι] {I : Ideal A} (P : Presentation A B I ι) {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n)
    (f : linearMapOfAlgHom I ψn P.toExtension.Cotangent) :
    ext1OfAlgHom.mk P ψn f = Quot.mk (Ext1Rel P ψn) f :=
  sorry

/-- The zero class in the Hom-coker model of `Ext¹` along `ψn`. -/
instance instZeroExt1OfAlgHom [Fintype ι] {I : Ideal A} (P : Presentation A B I ι)
    {n : ℕ} (ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n) :
    Zero (ext1OfAlgHom P ψn) where
  zero := ext1OfAlgHom.mk P ψn (linearMapOfAlgHom.mk ψn fun _ ↦ 0)

/-- The obstruction homomorphism `o(ψ) : J / J² → I^n C / I^{2n} C` sending the
residue of `g ∈ J` to the class of `ψ g`. -/
def obstructionHom {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    linearMapOfAlgHom I ψn P.toExtension.Cotangent :=
  linearMapOfAlgHom.mk ψn fun x ↦
    Ideal.mapCotangent P.ker (I.map (algebraMap A C) ^ n) ψ (IsLift.ker_le_comap hψ)
      (Cotangent.val x)

/-- `o(ψ)` evaluates on the residue of `g ∈ J` as the class of `ψ g`. -/
theorem obstructionHom_apply {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ)
    {g : polynomialCompletion A I ι} (hg : g ∈ P.ker) :
    obstructionHom hψ (Cotangent.mk ⟨g, hg⟩) =
      toAdicPowQuotient I C n ⟨ψ g, IsLift.mem_map_pow hψ hg⟩ :=
  sorry

/-- The obstruction class `o(ψn)` of a residue map, as the image of `o(ψ)` in
`Ext¹_B(NL_{B/A}^∧, I^n C / I^{2n} C)`. -/
def obstructionClass [Fintype ι] {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    ext1OfAlgHom P ψn :=
  ext1OfAlgHom.mk P ψn (obstructionHom hψ)

/-- `o(ψn)` is the class of `o(ψ)` in the Hom-coker model of `Ext¹`. -/
theorem obstructionClass_mk [Fintype ι] {I : Ideal A} {P : Presentation A B I ι} {n : ℕ}
    {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    obstructionClass hψ = ext1OfAlgHom.mk P ψn (obstructionHom hψ) :=
  sorry

/-- The obstruction class vanishes iff `o(ψ)` factors through the Jacobian. -/
theorem obstructionClass_eq_zero_iff [Fintype ι] {I : Ideal A} {P : Presentation A B I ι}
    {n : ℕ} {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    obstructionClass hψ = 0 ↔
      ∃ h : linearMapOfAlgHom I ψn (ι → B),
        obstructionHom hψ = jacobianHomOfAlgHom P ψn h :=
  sorry

/-- Coefficient change `I^n C / I^{2n} C → I^{n'} C / I^{2n'} C` induced by
`n' ≤ n`, hence `I^n C ⊆ I^{n'} C` and `I^{2n} C ⊆ I^{2n'} C`. -/
def map_adicPowQuotient (I : Ideal A) {n n' : ℕ} (h : n' ≤ n) :
    adicPowQuotient I C n →ₗ[C] adicPowQuotient I C n' :=
  Ideal.mapCotangent (I.map (algebraMap A C) ^ n) (I.map (algebraMap A C) ^ n')
    (AlgHom.id C C) fun _ hx ↦ Ideal.pow_le_pow_right h hx

/-- Coefficient change sends the class of `x ∈ I^n C` to its class in `I^{n'} C / I^{2n'} C`. -/
theorem map_adicPowQuotient_apply (I : Ideal A) {n n' : ℕ} (h : n' ≤ n) {x : C}
    (hx : x ∈ I.map (algebraMap A C) ^ n) :
    map_adicPowQuotient I h (toAdicPowQuotient I C n ⟨x, hx⟩) =
      toAdicPowQuotient I C n' ⟨x, Ideal.pow_le_pow_right h hx⟩ :=
  sorry

/-- Coefficient change of the obstruction homomorphism `o(ψ)` along `n' ≤ n`. -/
def map_obstructionHom [Fintype ι] {I : Ideal A} {P : Presentation A B I ι} {n n' : ℕ}
    (h : n' ≤ n) {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    linearMapOfAlgHom I ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)).comp ψn)
      P.toExtension.Cotangent :=
  linearMapOfAlgHom.mk ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)).comp ψn)
    fun x ↦ map_adicPowQuotient I h (obstructionHom hψ x)

/-- Coefficient change of `o(ψ)` is `map_adicPowQuotient` after `o(ψ)`. -/
theorem map_obstructionHom_apply [Fintype ι] {I : Ideal A} {P : Presentation A B I ι}
    {n n' : ℕ} (h : n' ≤ n) {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ)
    (x : P.toExtension.Cotangent) :
    map_obstructionHom h hψ x = map_adicPowQuotient I h (obstructionHom hψ x) :=
  sorry

/-- The image of `o(ψn)` in `Ext¹_B(NL_{B/A}^∧, I^{n'} C / I^{2n'} C)` along coefficient
change `n' ≤ n`. -/
def map_obstructionClass [Fintype ι] {I : Ideal A} {P : Presentation A B I ι} {n n' : ℕ}
    (h : n' ≤ n) {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    ext1OfAlgHom P ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)).comp ψn) :=
  ext1OfAlgHom.mk P ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)).comp ψn)
    (map_obstructionHom h hψ)

/-- Coefficient change of obstruction classes is the class of `map_obstructionHom`. -/
theorem map_obstructionClass_mk [Fintype ι] {I : Ideal A} {P : Presentation A B I ι}
    {n n' : ℕ} (h : n' ≤ n) {ψn : B →ₐ[A] C ⧸ I.map (algebraMap A C) ^ n}
    {ψ : polynomialCompletion A I ι →ₐ[A] C} (hψ : IsLift P ψn ψ) :
    map_obstructionClass h hψ =
      ext1OfAlgHom.mk P ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)).comp ψn)
        (map_obstructionHom h hψ) :=
  sorry

end Algebra.NaiveCotangent.Adic
