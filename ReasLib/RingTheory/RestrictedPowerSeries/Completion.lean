/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Polynomial.Quotient
public import ReasLib.RingTheory.RestrictedPowerSeries
public import ReasLib.RingTheory.AdicCompletion.Polynomial
public import ReasLib.RingTheory.Topology.Adic.Complete

/-! # Restricted power series and ideal-adic polynomial completion -/

@[expose] public section

open TopologicalRing
open TopologicalRing.Ideal

noncomputable section

universe u

namespace RestrictedPowerSeries

variable {A : Type u} [CommRing A] [TopologicalSpace A]

variable (ι : Type u) (I : Ideal A)

/-- The least power of an ideal of definition contained in a given open ideal. -/
private def powIndex (hI : IsIdealOfDefinition I) (J : OpenIdeal A) : ℕ :=
  by
    classical
    exact Nat.find (hI.2 (J.1 : Set A) (J.2.mem_nhds J.1.zero_mem))

/-- The least cofinal exponent gives containment in the specified open ideal. -/
private theorem powIndex_le (hI : IsIdealOfDefinition I) (J : OpenIdeal A) :
    I ^ powIndex I hI J ≤ J.1 :=
  by
    classical
    exact Nat.find_spec (hI.2 (J.1 : Set A) (J.2.mem_nhds J.1.zero_mem))

section Components

variable [IsTopologicalRing A] [IsLinearTopology A A]

/-- Evaluation at an open ideal as an algebra map over the coefficient ring. -/
def componentAlgHom (J : OpenIdeal A) :
    RestrictedPowerSeries ι A →ₐ[A] MvPolynomial ι (A ⧸ J.1) where
  __ := component J
  commutes' a := by
    change MvPolynomial.map (Ideal.Quotient.mk J.1) (MvPolynomial.C a) = _
    rw [MvPolynomial.map_C]
    rfl

/-- The component algebra map evaluates the underlying component family. -/
theorem componentAlgHom_apply (J : OpenIdeal A) (f : RestrictedPowerSeries ι A) :
    componentAlgHom ι J f = component J f := rfl

end Components

omit [TopologicalSpace A] in
private theorem quotientPolynomial_symm_mk (J : Ideal A) (p : MvPolynomial ι A) :
    (MvPolynomial.quotientEquivQuotientMvPolynomial J).symm
        (Ideal.Quotient.mk (J.map MvPolynomial.C) p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]
  rfl

omit [TopologicalSpace A] in
private theorem quotientPolynomial_map_mk (J : Ideal A) (p : MvPolynomial ι A) :
    MvPolynomial.quotientEquivQuotientMvPolynomial J
        (MvPolynomial.map (Ideal.Quotient.mk J) p) =
      Ideal.Quotient.mk (J.map MvPolynomial.C) p := by
  apply (MvPolynomial.quotientEquivQuotientMvPolynomial J).symm.injective
  rw [AlgEquiv.symm_apply_apply, quotientPolynomial_symm_mk]

private theorem factor_eval_adic {R : Type u} [CommRing R] (J : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (F : AdicCompletion J R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ J n F) =
      AdicCompletion.evalₐ J m F := by
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
      (Ideal.quotientEquivAlgOfEq R (by simp : (J ^ n • ⊤ : Ideal R) = J ^ n) (F.val n)) =
    Ideal.quotientEquivAlgOfEq R (by simp : (J ^ m • ⊤ : Ideal R) = J ^ m) (F.val m)
  rw [← F.property hmn]
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (F.val n)
  rw [← hp]
  rfl

omit [TopologicalSpace A] in
private theorem stageHom_compatible {m n : ℕ} (hmn : m ≤ n)
    (F : IAdicRestrictedPowerSeries ι I) :
    MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn))
        (IAdicRestrictedPowerSeries.stageHom ι I n F) =
      IAdicRestrictedPowerSeries.stageHom ι I m F := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (I.map (MvPolynomial.C (σ := ι))) n F)
  have hm := factor_eval_adic (I.map (MvPolynomial.C (σ := ι))) hmn F
  rw [← hp] at hm
  change MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn))
      ((MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm
        (Ideal.quotientEquivAlgOfEq A (Ideal.map_pow (MvPolynomial.C (σ := ι)) I n).symm
          (AdicCompletion.evalₐ (I.map (MvPolynomial.C (σ := ι))) n F))) =
    (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ m)).symm
      (Ideal.quotientEquivAlgOfEq A (Ideal.map_pow (MvPolynomial.C (σ := ι)) I m).symm
        (AdicCompletion.evalₐ (I.map (MvPolynomial.C (σ := ι))) m F))
  rw [← hp, ← hm, Ideal.Quotient.factor_mk, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientEquivAlgOfEq_mk, quotientPolynomial_symm_mk, quotientPolynomial_symm_mk,
    MvPolynomial.map_map, Ideal.Quotient.factor_comp_mk]

variable [IsAdicRing A]

/-- A power of an ideal of definition, bundled as an open ideal. -/
private def openPow (hI : IsIdealOfDefinition I) (n : ℕ) : OpenIdeal A :=
  ⟨I ^ n, (isAdic_iff.mp hI.isAdic).1 n⟩

/-- The finite-stage map from restricted power series to a polynomial quotient. -/
private def toAdicStage (hI : IsIdealOfDefinition I) (n : ℕ) :
    RestrictedPowerSeries ι A →ₐ[A]
      MvPolynomial ι A ⧸ (I.map (algebraMap A (MvPolynomial ι A))) ^ n :=
  (Ideal.quotientEquivAlgOfEq A
      (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n)).toAlgHom.comp
    ((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) (I ^ n)).toAlgHom.comp
      (componentAlgHom ι (openPow I hI n)))

/-- Finite-stage comparison maps commute with adic transition maps. -/
private theorem toAdicStage_compatible (hI : IsIdealOfDefinition I) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp
      (toAdicStage ι I hI n) =
      toAdicStage ι I hI m := by
  apply AlgHom.ext
  intro f
  obtain ⟨p, hp⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk (I ^ n))
    Ideal.Quotient.mk_surjective (component (openPow I hI n) f)
  have hm := f.2 (openPow I hI n) (openPow I hI m) (Ideal.pow_le_pow_right hle)
  change MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right hle))
      (component (openPow I hI n) f) = component (openPow I hI m) f at hm
  dsimp only [openPow] at hp hm
  erw [← hp, MvPolynomial.map_map, Ideal.Quotient.factor_comp_mk] at hm
  change Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)
      (Ideal.quotientEquivAlgOfEq A (Ideal.map_pow (MvPolynomial.C (σ := ι)) I n)
        (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)
          (component (openPow I hI n) f))) =
    Ideal.quotientEquivAlgOfEq A (Ideal.map_pow (MvPolynomial.C (σ := ι)) I m)
      (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ m)
        (component (openPow I hI m) f))
  dsimp only [openPow]
  erw [← hp, ← hm, quotientPolynomial_map_mk, quotientPolynomial_map_mk]
  rfl

/-- The canonical stagewise algebra map to the ideal-adic polynomial completion. -/
@[no_expose] def toAdicAlgHom (hI : IsIdealOfDefinition I) :
    RestrictedPowerSeries ι A →ₐ[A] IAdicRestrictedPowerSeries ι I :=
  AdicCompletion.liftAlgHom (I.map (algebraMap A (MvPolynomial ι A)))
    (toAdicStage ι I hI) (toAdicStage_compatible ι I hI)

/-- Evaluation of the comparison at an adic stage is its finite-stage map. -/
private theorem eval_toAdicAlgHom (hI : IsIdealOfDefinition I) (n : ℕ)
    (f : RestrictedPowerSeries ι A) :
    AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial ι A))) n
        (toAdicAlgHom ι I hI f) =
      toAdicStage ι I hI n f :=
  AdicCompletion.evalₐ_liftAlgHom _ _ _ n f

private theorem stageHom_toAdicAlgHom (hI : IsIdealOfDefinition I) (n : ℕ)
    (f : RestrictedPowerSeries ι A) :
    IAdicRestrictedPowerSeries.stageHom ι I n (toAdicAlgHom ι I hI f) =
      component (openPow I hI n) f := by
  change (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm
      (Ideal.quotientEquivAlgOfEq A
        (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n).symm
        (AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial ι A))) n
          (toAdicAlgHom ι I hI f))) = _
  rw [eval_toAdicAlgHom]
  change (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm
      (Ideal.quotientEquivAlgOfEq A
        (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n).symm
        (Ideal.quotientEquivAlgOfEq A
          (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n)
          (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)
            (component (openPow I hI n) f)))) = _
  rw [← Ideal.quotientEquivAlgOfEq_symm A
    (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n), AlgEquiv.symm_apply_apply,
    AlgEquiv.symm_apply_apply]

/-- The cofinal component family of a completed polynomial is compatible. -/
private theorem ofAdic_compatible (hI : IsIdealOfDefinition I)
    (F : IAdicRestrictedPowerSeries ι I) :
    Compatible fun J : OpenIdeal A ↦
      MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))
        (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J) F) := by
  intro J K hJK
  dsimp only
  let n := max (powIndex I hI J) (powIndex I hI K)
  have hJ := stageHom_compatible ι I
    (show powIndex I hI J ≤ n from le_max_left _ _) F
  have hK := stageHom_compatible ι I
    (show powIndex I hI K ≤ n from le_max_right _ _) F
  rw [← hJ, ← hK]
  simp only [MvPolynomial.map_map, Ideal.Quotient.factor_comp]

/-- The restricted series whose open-ideal components are the cofinal polynomial stages. -/
private def ofAdic (hI : IsIdealOfDefinition I) (F : IAdicRestrictedPowerSeries ι I) :
    RestrictedPowerSeries ι A :=
  ⟨fun J ↦
    MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))
      (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J) F),
    ofAdic_compatible ι I hI F⟩

/-- The components of the inverse comparison are the cofinal polynomial stages. -/
private theorem ofAdic_component (hI : IsIdealOfDefinition I)
    (F : IAdicRestrictedPowerSeries ι I) (J : OpenIdeal A) :
    component J (ofAdic ι I hI F) =
      MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))
        (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J) F) := rfl

private theorem ofAdic_component_openPow (hI : IsIdealOfDefinition I)
    (F : IAdicRestrictedPowerSeries ι I) (n : ℕ) :
    component (openPow I hI n) (ofAdic ι I hI F) =
      IAdicRestrictedPowerSeries.stageHom ι I n F := by
  rw [ofAdic_component]
  let k := powIndex I hI (openPow I hI n)
  have hk := stageHom_compatible ι I
    (le_max_left k n) F
  have hn := stageHom_compatible ι I
    (le_max_right k n) F
  rw [← hk, ← hn]
  simp only [MvPolynomial.map_map, Ideal.Quotient.factor_comp]
  rfl

/-- The algebra map from the polynomial completion to restricted power series. -/
@[no_expose] def ofAdicAlgHom (hI : IsIdealOfDefinition I) :
    IAdicRestrictedPowerSeries ι I →ₐ[A] RestrictedPowerSeries ι A where
  toFun := ofAdic ι I hI
  map_one' := by
    apply Subtype.ext
    funext J
    exact map_one ((MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))).comp
      (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J)).toRingHom)
  map_mul' F G := by
    apply Subtype.ext
    funext J
    exact map_mul ((MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))).comp
      (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J)).toRingHom) F G
  map_zero' := by
    apply Subtype.ext
    funext J
    exact map_zero ((MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))).comp
      (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J)).toRingHom)
  map_add' F G := by
    apply Subtype.ext
    funext J
    exact map_add ((MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))).comp
      (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J)).toRingHom) F G
  commutes' a := by
    apply Subtype.ext
    funext J
    change MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))
        (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J)
          (algebraMap A (IAdicRestrictedPowerSeries ι I) a)) =
      MvPolynomial.map (Ideal.Quotient.mk J.1) (MvPolynomial.C a)
    rw [AlgHom.commutes]
    change MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))
        (MvPolynomial.C (Ideal.Quotient.mk (I ^ powIndex I hI J) a)) = _
    simp

/-- The inverse algebra map has the specified cofinal component family. -/
private theorem ofAdicAlgHom_apply (hI : IsIdealOfDefinition I)
    (F : IAdicRestrictedPowerSeries ι I) :
    ofAdicAlgHom ι I hI F = ofAdic ι I hI F := rfl

/-- Restricted power series are canonically equivalent to the polynomial
completion along an ideal of definition. -/
def adicEquiv (hI : IsIdealOfDefinition I) :
    RestrictedPowerSeries ι A ≃ₐ[A] IAdicRestrictedPowerSeries ι I :=
  AlgEquiv.ofAlgHom (toAdicAlgHom ι I hI) (ofAdicAlgHom ι I hI)
    (by
      apply AlgHom.ext
      intro F
      apply AdicCompletion.ext_evalₐ
      intro n
      change AdicCompletion.evalₐ _ n
          (toAdicAlgHom ι I hI (ofAdicAlgHom ι I hI F)) =
        AdicCompletion.evalₐ _ n F
      rw [eval_toAdicAlgHom]
      change Ideal.quotientEquivAlgOfEq A
          (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n)
          (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)
            (component (openPow I hI n) (ofAdic ι I hI F))) = _
      rw [ofAdic_component_openPow]
      change Ideal.quotientEquivAlgOfEq A
          (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n)
          (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)
            ((MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm
              (Ideal.quotientEquivAlgOfEq A
                (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n).symm
                (AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial ι A))) n F)))) = _
      rw [AlgEquiv.apply_symm_apply, ← Ideal.quotientEquivAlgOfEq_symm A
        (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n),
        AlgEquiv.apply_symm_apply])
    (by
      apply AlgHom.ext
      intro f
      apply Subtype.ext
      funext J
      change MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))
          (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J)
            (toAdicAlgHom ι I hI f)) = component J f
      rw [stageHom_toAdicAlgHom]
      exact f.2 (openPow I hI (powIndex I hI J)) J (powIndex_le I hI J))

/-- The canonical equivalence sends a restricted polynomial to its completion. -/
theorem adicEquiv_ofPolynomial (hI : IsIdealOfDefinition I) (g : MvPolynomial ι A) :
    adicEquiv ι I hI (ofPolynomial g) =
      AdicCompletion.of (I.map (algebraMap A (MvPolynomial ι A))) (MvPolynomial ι A) g := by
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ _ n (toAdicAlgHom ι I hI (ofPolynomial g)) = _
  rw [eval_toAdicAlgHom, AdicCompletion.evalₐ_of]
  change Ideal.quotientEquivAlgOfEq A
      (Ideal.map_pow (MvPolynomial.C (σ := ι)) I n)
      (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)
        (MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) g)) = _
  rw [quotientPolynomial_map_mk, Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- The canonical equivalence sends restricted variables to completed variables. -/
theorem adicEquiv_X (hI : IsIdealOfDefinition I) (i : ι) :
    adicEquiv ι I hI (ofPolynomial (MvPolynomial.X i)) =
      AdicCompletion.of (I.map (algebraMap A (MvPolynomial ι A)))
        (MvPolynomial ι A) (MvPolynomial.X i) :=
  adicEquiv_ofPolynomial ι I hI (MvPolynomial.X i)

end RestrictedPowerSeries
