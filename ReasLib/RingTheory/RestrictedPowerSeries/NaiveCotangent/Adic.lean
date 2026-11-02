/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.RestrictedPowerSeries.NaiveCotangent.Homotopy
public import ReasLib.RingTheory.RestrictedPowerSeries.Completion
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent

-- The finite-stage calculation uses the concrete implementation of the comparison map.
import all ReasLib.RingTheory.RestrictedPowerSeries.Completion

/-! # Comparison of restricted and ideal-adic naive cotangent complexes -/

@[expose] public section

open Algebra.Extension
open CategoryTheory
open HomotopyCategory
open RestrictedPowerSeries
open TopologicalRing
open TopologicalRing.Ideal

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Restricted

section Comparison

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsAdicRing A]
variable (ι : Type u) (I : Ideal A)

variable {B : Type u} [CommRing B] [Algebra A B]

namespace Presentation

/-- The `I`-adic completed polynomial presentation associated with a restricted
presentation along the canonical restricted-to-adic equivalence. -/
def toAdic (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    Algebra.NaiveCotangent.Adic.Presentation A B I ι :=
  Algebra.NaiveCotangent.Adic.Presentation.ofSurjective
    (P.toAlgHom.comp (adicEquiv ι I hI).symm.toAlgHom)
    (P.surjective.comp (adicEquiv ι I hI).symm.surjective)

/-- The structure map of `toAdic` is the restricted structure map composed with
the inverse identification. -/
theorem toAdic_toAlgHom (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    (toAdic ι I hI P).toAlgHom = P.toAlgHom.comp (adicEquiv ι I hI).symm.toAlgHom :=
  rfl

/-- Compatibility of `adicEquiv` with the two structure maps to `B`. -/
private theorem toAdicExtensionHom_commutes (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (IsScalarTower.toAlgHom A (toAdic ι I hI P).toExtension.Ring B).comp
        (adicEquiv ι I hI).toAlgHom =
      (IsScalarTower.toAlgHom A B B).comp
        (IsScalarTower.toAlgHom A P.toExtension.Ring B) :=
  by
    ext x
    change P.toAlgHom ((adicEquiv ι I hI).symm (adicEquiv ι I hI x)) = P.toAlgHom x
    rw [AlgEquiv.symm_apply_apply]

/-- The morphism of extensions induced by `adicEquiv`. -/
@[no_expose] def toAdicExtensionHom (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    P.toExtension.Hom (toAdic ι I hI P).toExtension :=
  Extension.Hom.ofAlgHom (adicEquiv ι I hI).toAlgHom
    (toAdicExtensionHom_commutes ι I hI P)

/-- Compatibility of `adicEquiv.symm` with the two structure maps to `B`. -/
private theorem ofAdicExtensionHom_commutes (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (IsScalarTower.toAlgHom A P.toExtension.Ring B).comp
        (adicEquiv ι I hI).symm.toAlgHom =
      (IsScalarTower.toAlgHom A B B).comp
        (IsScalarTower.toAlgHom A (toAdic ι I hI P).toExtension.Ring B) :=
  by
    ext x
    rfl

/-- The morphism of extensions induced by `adicEquiv.symm`. -/
@[no_expose] def ofAdicExtensionHom (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    (toAdic ι I hI P).toExtension.Hom P.toExtension :=
  Extension.Hom.ofAlgHom (adicEquiv ι I hI).symm.toAlgHom
    (ofAdicExtensionHom_commutes ι I hI P)

/-- Inverse laws for the conormal maps induced by `adicEquiv`. -/
private theorem cotangentIso_toAdic_comp (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (Cotangent.map (toAdicExtensionHom ι I hI P)).comp
        (Cotangent.map (ofAdicExtensionHom ι I hI P)) =
      LinearMap.id :=
  by
    ext x
    obtain ⟨g, rfl⟩ := Cotangent.mk_surjective x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Cotangent.map_mk]
    apply congrArg (Cotangent.mk (P := (toAdic ι I hI P).toExtension))
    apply Subtype.ext
    exact (adicEquiv ι I hI).apply_symm_apply _

/-- Inverse laws for the conormal maps induced by `adicEquiv.symm`. -/
private theorem cotangentIso_ofAdic_comp (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (Cotangent.map (ofAdicExtensionHom ι I hI P)).comp
        (Cotangent.map (toAdicExtensionHom ι I hI P)) =
      LinearMap.id :=
  by
    ext x
    obtain ⟨g, rfl⟩ := Cotangent.mk_surjective x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Cotangent.map_mk]
    apply congrArg (Cotangent.mk (P := P.toExtension))
    apply Subtype.ext
    exact (adicEquiv ι I hI).symm_apply_apply _

/-- The canonical identification of conormal modules along `adicEquiv`. -/
@[no_expose] def cotangentIso_toAdic (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    P.toExtension.Cotangent ≃ₗ[B]
      (toAdic ι I hI P).toExtension.Cotangent :=
  LinearEquiv.ofLinear
    (Cotangent.map (toAdicExtensionHom ι I hI P))
    (Cotangent.map (ofAdicExtensionHom ι I hI P))
    (cotangentIso_toAdic_comp ι I hI P)
    (cotangentIso_ofAdic_comp ι I hI P)

end Presentation

private theorem adicEquiv_stage (hI : IsIdealOfDefinition I) (n : ℕ)
    (f : RestrictedPowerSeries ι A) :
    IAdicRestrictedPowerSeries.stageHom ι I n (adicEquiv ι I hI f) =
      component (⟨I ^ n, (isAdic_iff.mp hI.isAdic).1 n⟩ : OpenIdeal A) f := by
  change (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm
      (Ideal.quotientEquivAlgOfEq A
        (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n).symm
        (AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial ι A))) n
          (toAdicAlgHom ι I hI f))) = _
  rw [toAdicAlgHom, AdicCompletion.evalₐ_liftAlgHom]
  change (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm
      (Ideal.quotientEquivAlgOfEq A
        (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n).symm
        (Ideal.quotientEquivAlgOfEq A
          (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n)
          (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)
            (component (⟨I ^ n, (isAdic_iff.mp hI.isAdic).1 n⟩ : OpenIdeal A) f)))) = _
  rw [← Ideal.quotientEquivAlgOfEq_symm A
    (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n), AlgEquiv.symm_apply_apply,
    AlgEquiv.symm_apply_apply]

omit [TopologicalSpace A] [IsAdicRing A] in
private theorem adicPderiv_stage (i : ι) (n : ℕ)
    (f : IAdicRestrictedPowerSeries ι I) :
    IAdicRestrictedPowerSeries.stageHom ι I n (Adic.pderiv I i f) =
      MvPolynomial.pderiv i (IAdicRestrictedPowerSeries.stageHom ι I n f) := by
  have hq (p : MvPolynomial ι A) :
      (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm
          (Ideal.Quotient.mk ((I ^ n).map MvPolynomial.C) p) =
        MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p := by
    rw [MvPolynomial.map_eq_eval₂Hom_C_comp]
    rfl
  change (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm
      (Ideal.quotientEquivAlgOfEq A
        (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n).symm
        (Ideal.quotientEquivAlgOfEq (MvPolynomial ι A)
          (by simp [Adic.polynomialIdeal_eq_map] : (Adic.polynomialIdeal A I ι ^ n • ⊤ : Ideal _) = _)
          (AdicCompletion.eval (Adic.polynomialIdeal A I ι) (MvPolynomial ι A) n
            (Adic.pderiv I i f)))) =
    MvPolynomial.pderiv i
      ((MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm
        (Ideal.quotientEquivAlgOfEq A
          (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n).symm
          (Ideal.quotientEquivAlgOfEq (MvPolynomial ι A)
            (by simp [Adic.polynomialIdeal_eq_map] : (Adic.polynomialIdeal A I ι ^ n • ⊤ : Ideal _) = _)
            (f.val n))))
  rw [Adic.eval_pderiv]
  simp only [AdicCompletion.eval_apply]
  generalize f.val n = x
  induction x using Quotient.inductionOn' with
  | h p =>
    change (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm
        (Ideal.Quotient.mk ((I ^ n).map MvPolynomial.C) (MvPolynomial.pderiv i p)) =
      MvPolynomial.pderiv i
        ((MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm
          (Ideal.Quotient.mk ((I ^ n).map MvPolynomial.C) p))
    rw [hq, hq, MvPolynomial.pderiv_map]

private theorem adicEquiv_pderiv (hI : IsIdealOfDefinition I) (i : ι)
    (f : RestrictedPowerSeries ι A) :
    Adic.pderiv I i (adicEquiv ι I hI f) = adicEquiv ι I hI (pderiv i f) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  apply (Ideal.quotientEquivAlgOfEq A
    (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n).symm).injective
  apply (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm.injective
  change IAdicRestrictedPowerSeries.stageHom ι I n (Adic.pderiv I i (adicEquiv ι I hI f)) =
    IAdicRestrictedPowerSeries.stageHom ι I n (adicEquiv ι I hI (pderiv i f))
  rw [adicPderiv_stage, adicEquiv_stage, adicEquiv_stage]
  rfl

variable [Fintype ι]

/-- Higher components of the `I`-adic Jacobian complex of a transported
restricted presentation are the zero object of `ModuleCat`. -/
private def adicComponentSuccIsoUnit (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) (n : ℕ) :
    (Adic.complex (Presentation.toAdic ι I hI P)).X (n + 2) ≅
      ModuleCat.of B PUnit :=
  ChainComplex.mk'XIso
    (ModuleCat.of B (ι → B))
    (ModuleCat.of B (Presentation.toAdic ι I hI P).toExtension.Cotangent)
    (ModuleCat.ofHom (Adic.jacobian (Presentation.toAdic ι I hI P)))
    (fun {_ _} _ ↦ ⟨ModuleCat.of B PUnit, 0, CategoryTheory.Limits.zero_comp⟩)
    n

/-- Components of the identification of restricted and `I`-adic Jacobian
complexes along `adicEquiv`. -/
private def toAdicIsoComponent (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    ∀ n, (complex P).X n ≅ (Adic.complex (Presentation.toAdic ι I hI P)).X n
  | 0 =>
    (componentZeroIso P).trans
      (Adic.componentZeroIso (Presentation.toAdic ι I hI P)).symm
  | 1 =>
    (componentOneIso P).trans (Presentation.cotangentIso_toAdic ι I hI P).toModuleIso
  | n + 2 =>
    (componentSuccIsoUnit P n).trans (adicComponentSuccIsoUnit ι I hI P n).symm

/-- The componentwise identification along `adicEquiv` commutes with
differentials. -/
private theorem toAdicIsoComponent_comm (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (toAdicIsoComponent ι I hI P i).hom ≫
        (Adic.complex (Presentation.toAdic ι I hI P)).d i j =
      (complex P).d i j ≫ (toAdicIsoComponent ι I hI P j).hom :=
  by
    change j + 1 = i at hij
    subst i
    cases j with
    | zero =>
      change ModuleCat.ofHom (Cotangent.map (Presentation.toAdicExtensionHom ι I hI P)) ≫
          (Adic.complex (Presentation.toAdic ι I hI P)).d 1 0 =
        (complex P).d 1 0 ≫ 𝟙 _
      rw [Adic.complex_d_one_zero, Category.comp_id]
      rw [show (complex P).d 1 0 = ModuleCat.ofHom (jacobian P) from
        ChainComplex.mk'_d_1_0 ..]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext k
      obtain ⟨g, rfl⟩ := Cotangent.mk_surjective x
      change Adic.jacobian (Presentation.toAdic ι I hI P)
          (Cotangent.map (Presentation.toAdicExtensionHom ι I hI P) (Cotangent.mk g)) k = _
      rw [Cotangent.map_mk, Adic.jacobian_apply]
      change P.toAlgHom ((adicEquiv ι I hI).symm
          (Adic.pderiv I k (adicEquiv ι I hI g.val))) =
        P.toAlgHom (pderiv k g.val)
      rw [adicEquiv_pderiv, AlgEquiv.symm_apply_apply]
    | succ j =>
      have hr : (complex P).d (j + 2) (j + 1) = 0 := by
        simp only [complex, ChainComplex.mk'_d, Limits.comp_zero]
        rfl
      have ha : (Adic.complex (Presentation.toAdic ι I hI P)).d (j + 2) (j + 1) = 0 := by
        simp only [Adic.complex, ChainComplex.mk'_d, Limits.comp_zero]
        rfl
      rw [hr, ha, Limits.zero_comp, Limits.comp_zero]

/-- The restricted Jacobian complex is canonically isomorphic to the `I`-adic
Jacobian complex of the transported presentation, via `adicEquiv`. -/
@[no_expose] def complexIso_toAdic (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    complex P ≅ Adic.complex (Presentation.toAdic ι I hI P) :=
  HomologicalComplex.Hom.isoOfComponents (toAdicIsoComponent ι I hI P)
    (toAdicIsoComponent_comm ι I hI P)

private theorem complexIso_toAdic_X_zero_eq (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (complexIso_toAdic ι I hI P).hom.f 0 =
      ((componentZeroIso P).trans
        (Adic.componentZeroIso (Presentation.toAdic ι I hI P)).symm).hom :=
  rfl

/-- The degree-zero component of `complexIso_toAdic` is the identity on
`ι → B`. -/
theorem complexIso_toAdic_X_zero (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (complexIso_toAdic ι I hI P).hom.f 0 =
      ((componentZeroIso P).trans
        (Adic.componentZeroIso (Presentation.toAdic ι I hI P)).symm).hom :=
  complexIso_toAdic_X_zero_eq ι I hI P

private theorem complexIso_toAdic_X_one_eq (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (complexIso_toAdic ι I hI P).hom.f 1 =
      ((componentOneIso P).trans
        (Presentation.cotangentIso_toAdic ι I hI P).toModuleIso).hom :=
  rfl

/-- The degree-one component of `complexIso_toAdic` is the conormal map of
`adicEquiv`. -/
theorem complexIso_toAdic_X_one (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (complexIso_toAdic ι I hI P).hom.f 1 =
      ((componentOneIso P).trans
        (Presentation.cotangentIso_toAdic ι I hI P).toModuleIso).hom :=
  complexIso_toAdic_X_one_eq ι I hI P

/-- The restricted Jacobian complex is homotopy equivalent to the `I`-adic
Jacobian complex of the transported presentation. -/
theorem complex_homotopyEquiv_toAdic (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    Nonempty
      (HomotopyEquiv (complex P)
        (Algebra.NaiveCotangent.Adic.complex (Presentation.toAdic ι I hI P))) :=
  ⟨HomotopyEquiv.ofIso (complexIso_toAdic ι I hI P)⟩

end Comparison

section IndependentOfIdeal

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A]
variable [CommRing B] [TopologicalSpace B] [Algebra A B]
variable {ι ι' : Type u} [Fintype ι] [Fintype ι']

/-- For an adic topologically finite-type arrow of adic-star rings with
Noetherian source, finite adic presentations along any two ideals of definition
give isomorphic naive cotangent complexes in the homotopy category. -/
theorem independentOfIdeal [IsAdicStarRing A] [IsAdicStarRing B]
    [IsNoetherianRing A]
    (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (I I' : Ideal A) (hI : IsIdealOfDefinition I) (hI' : IsIdealOfDefinition I')
    (P_adic : Adic.Presentation A B I ι)
    (Q_adic : Adic.Presentation A B I' ι') :
    Nonempty
      ((quotient (ModuleCat B) (ComplexShape.down ℕ)).obj
          (Adic.naiveCotangent I P_adic) ≅
        (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj
          (Adic.naiveCotangent I' Q_adic)) :=
  sorry

end IndependentOfIdeal

end Algebra.NaiveCotangent.Restricted
