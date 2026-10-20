/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Filtration
public import ReasLib.Algebra.Module.LocalizedModule.Kernel
public import ReasLib.Algebra.Module.LocalizedModule.Submodule
public import ReasLib.RingTheory.Flatness.IdealTensor
public import ReasLib.RingTheory.Flatness.QuotientPowers
public import ReasLib.RingTheory.Algebra.TensorProduct.Finite
public import ReasLib.RingTheory.Ideal.Tensor.Map
public import ReasLib.RingTheory.Ideal.KrullIntersection.Localization
public import ReasLib.RingTheory.Localization.AtPrime.Module
public import ReasLib.RingTheory.Localization.TensorProduct

/-!
# Ideal-tensor kernels from flat quotient powers

This leaf contains the adic filtration argument used by the prime-local
criterion for `Module.Flat.QuotientPowers`.  Its public surface is the
resulting bound on the kernel of ideal-tensor multiplication; the quotient
and base-change comparisons used to prove that bound remain private.

@stack 0523
-/

@[expose] public section

open scoped TensorProduct Pointwise

universe u v

namespace Module.Flat.QuotientPowers

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

private lemma ideal_pow_smul_top_eq_submoduleOf_pow_succ
    (I : Ideal R) (n : ℕ) :
    I ^ n • (⊤ : Submodule R I) = (I ^ (n + 1)).submoduleOf I := by
  ext x
  rw [Submodule.mem_smul_top_iff]
  change (x : R) ∈ I ^ n • I ↔ (x : R) ∈ I ^ (n + 1)
  rw [Ideal.smul_eq_mul, pow_succ]

private noncomputable def idealQuotientInfEquivMapQuotient
    (K J : Ideal R) :
    (J ⧸ (J ⊓ K).submoduleOf J) ≃ₗ[R]
      (((Ideal.map (Ideal.Quotient.mk K) J : Ideal (R ⧸ K)) :
        Submodule (R ⧸ K) (R ⧸ K)).restrictScalars R) := by
  let q : J →ₗ[R] (R ⧸ K) :=
    { toFun := fun x ↦ Ideal.Quotient.mk K x.1
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hker : LinearMap.ker q = (J ⊓ K).submoduleOf J := by
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      exact ⟨x.2, Ideal.Quotient.eq_zero_iff_mem.mp hx⟩
    · intro hx
      rw [LinearMap.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx.2
  have hrange :
      LinearMap.range q =
        (((Ideal.map (Ideal.Quotient.mk K) J : Ideal (R ⧸ K)) :
          Submodule (R ⧸ K) (R ⧸ K)).restrictScalars R) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Ideal.mem_map_of_mem (Ideal.Quotient.mk K) x.2
    · intro hy
      rcases
          (Ideal.mem_map_iff_of_surjective
            (f := Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective).1 hy with
        ⟨x, hxJ, rfl⟩
      exact ⟨⟨x, hxJ⟩, rfl⟩
  exact
    (Submodule.quotEquivOfEq (LinearMap.ker q) ((J ⊓ K).submoduleOf J) hker).symm.trans
      (q.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

private noncomputable def idealQuotientEquivMappedStage
    (I : Ideal R) (n : ℕ) :
    (I ⧸ (I ^ (n + 1)).submoduleOf I) ≃ₗ[R]
      (((Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I :
          Ideal (R ⧸ I ^ (n + 1))) :
        Submodule (R ⧸ I ^ (n + 1)) (R ⧸ I ^ (n + 1))).restrictScalars R) := by
  have hpow : I ^ (n + 1) ≤ I := Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hsub :
      ((I ⊓ I ^ (n + 1)).submoduleOf I) = (I ^ (n + 1)).submoduleOf I := by
    ext x
    constructor
    · exact fun hx ↦ hx.2
    · exact fun hx ↦ ⟨x.2, hx⟩
  exact
    (Submodule.quotEquivOfEq _ _ hsub).symm.trans
      (idealQuotientInfEquivMapQuotient (R := R) (K := I ^ (n + 1)) (J := I))

private noncomputable def idealQuotientTensorMappedStage
    (I : Ideal R) (n : ℕ) :
    (I ⧸ (I ^ (n + 1)).submoduleOf I) ⊗[R] M ≃ₗ[R]
      ((((Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I :
            Ideal (R ⧸ I ^ (n + 1))) :
          Submodule (R ⧸ I ^ (n + 1)) (R ⧸ I ^ (n + 1))).restrictScalars R) ⊗[R] M) :=
  TensorProduct.congr
    (idealQuotientEquivMappedStage (R := R) I n)
    (LinearEquiv.refl R M)

private noncomputable def mappedStageRightTensorEquiv
    (I : Ideal R) (n : ℕ) :
    ((((Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I : Ideal (R ⧸ I ^ (n + 1))) :
          Submodule (R ⧸ I ^ (n + 1)) (R ⧸ I ^ (n + 1))).restrictScalars R) ⊗[R] M) ≃ₗ[R ⧸ I ^ (n + 1)]
      (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I ⊗[R ⧸ I ^ (n + 1)]
        (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))) := by
  let A : Type u := R ⧸ I ^ (n + 1)
  let J : Ideal A := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I
  let eM : A ⊗[R] M ≃ₗ[A] M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)) :=
    LinearEquiv.extendScalarsOfSurjective (R := R) (S := A)
      Ideal.Quotient.mk_surjective (TensorProduct.quotTensorEquivQuotSMul M (I ^ (n + 1)))
  exact
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R A A
        (((J : Submodule A A).restrictScalars R)) M).symm).trans
      (TensorProduct.congr (LinearEquiv.refl A (J : Submodule A A)) eM)

private noncomputable def idealQuotientTensorStageEquiv
    (I : Ideal R) (n : ℕ) :
    (I ⧸ (I ^ (n + 1)).submoduleOf I) ⊗[R] M ≃ₗ[R]
      (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I ⊗[R ⧸ I ^ (n + 1)]
        (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))) :=
  (idealQuotientTensorMappedStage (R := R) (M := M) I n).trans
    ((mappedStageRightTensorEquiv (R := R) (M := M) I n).restrictScalars R)

private theorem idealQuotientTensorStageEquiv_tmul_mk
    (I : Ideal R) (n : ℕ) (a : I) (m : M) :
    idealQuotientTensorStageEquiv (R := R) (M := M) I n
        ((Submodule.Quotient.mk a) ⊗ₜ[R] m) =
      (idealQuotientEquivMappedStage (R := R) I n (Submodule.Quotient.mk a)) ⊗ₜ[R ⧸
        I ^ (n + 1)] (Submodule.Quotient.mk m) := by
  simp [idealQuotientTensorStageEquiv, idealQuotientTensorMappedStage,
    mappedStageRightTensorEquiv]
  rfl

private lemma idealQuotientScalarAction_ker
    (I : Ideal R) (n : ℕ) :
    (I ^ (n + 1)).submoduleOf I ≤
      LinearMap.ker
        ((LinearMap.compRight R (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
          ((LinearMap.lsmul R M).comp I.subtype)) := by
  intro a ha
  ext m
  exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul ha (by simp))

private noncomputable def idealQuotientScalarAction
    (I : Ideal R) (n : ℕ) :
    (I ⧸ (I ^ (n + 1)).submoduleOf I) →ₗ[R]
      (M →ₗ[R] M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) :=
  Submodule.liftQ
    ((I ^ (n + 1)).submoduleOf I)
    ((LinearMap.compRight R (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
      ((LinearMap.lsmul R M).comp I.subtype))
    (idealQuotientScalarAction_ker (R := R) (M := M) I n)

private noncomputable def idealQuotientTensorMul
    (I : Ideal R) (n : ℕ) :
    (I ⧸ (I ^ (n + 1)).submoduleOf I) ⊗[R] M →ₗ[R]
      M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)) :=
  TensorProduct.lift (idealQuotientScalarAction (R := R) (M := M) I n)

@[simp] private theorem idealQuotientTensorMul_tmul_mk
    (I : Ideal R) (n : ℕ) (a : I) (m : M) :
    idealQuotientTensorMul (R := R) (M := M) I n
        ((Submodule.Quotient.mk a) ⊗ₜ[R] m) =
      Submodule.Quotient.mk ((a : R) • m) := by
  simp [idealQuotientTensorMul, idealQuotientScalarAction]

private lemma stageTensorMul_comp_stageEquiv
    (I : Ideal R) (n : ℕ) :
    (TensorProduct.lift
      ((LinearMap.lsmul (R ⧸ I ^ (n + 1))
          (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
        (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I).subtype)).restrictScalars R ∘ₗ
        (idealQuotientTensorStageEquiv (R := R) (M := M) I n).toLinearMap =
      idealQuotientTensorMul (R := R) (M := M) I n := by
  apply TensorProduct.ext'
  intro q m
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective ((I ^ (n + 1)).submoduleOf I) q
  have hstage :
      idealQuotientTensorStageEquiv (R := R) (M := M) I n
          ((((I ^ (n + 1)).submoduleOf I).mkQ a) ⊗ₜ[R] m) =
        (idealQuotientEquivMappedStage (R := R) I n
            (((I ^ (n + 1)).submoduleOf I).mkQ a)) ⊗ₜ[R ⧸ I ^ (n + 1)]
          (Submodule.Quotient.mk m) := by
    simpa using idealQuotientTensorStageEquiv_tmul_mk (R := R) (M := M) I n a m
  change
    (TensorProduct.lift
      ((LinearMap.lsmul (R ⧸ I ^ (n + 1))
          (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
        (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I).subtype)).restrictScalars R
          (idealQuotientTensorStageEquiv (R := R) (M := M) I n
            ((((I ^ (n + 1)).submoduleOf I).mkQ a) ⊗ₜ[R] m)) =
      idealQuotientTensorMul (R := R) (M := M) I n
        ((((I ^ (n + 1)).submoduleOf I).mkQ a) ⊗ₜ[R] m)
  rw [hstage]
  rfl

private lemma idealQuotientTensorMul_comp_quotientTensorEquiv_symm_mkQ
    (I : Ideal R) (n : ℕ) :
    idealQuotientTensorMul (R := R) (M := M) I n ∘ₗ
        (TensorProduct.quotientTensorEquiv M ((I ^ (n + 1)).submoduleOf I)).symm.toLinearMap ∘ₗ
        Submodule.mkQ
          (LinearMap.range
            (TensorProduct.map ((I ^ (n + 1)).submoduleOf I).subtype
              (LinearMap.id : M →ₗ[R] M))) =
      (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ ∘ₗ I.tensorMul M := by
  apply TensorProduct.ext'
  intro a m
  simp [Ideal.tensorMul]

private lemma stageTensorMul_injective
    (I : Ideal R) (hflat : Module.Flat.QuotientPowers (M := M) I) (n : ℕ) :
    Function.Injective
      (TensorProduct.lift
        ((LinearMap.lsmul (R ⧸ I ^ (n + 1))
            (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
          (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I).subtype)) := by
  simpa [Ideal.tensorMul] using
    Module.Flat.tensorMul_injective
      (hflat (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
      (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I)

private lemma range_subtype_rTensor_le_smul_top
    (I : Ideal R) (N : Submodule R I) (J : Ideal R)
    (hN : N ≤ J • (⊤ : Submodule R I)) :
    LinearMap.range (N.subtype.rTensor M) ≤ J • (⊤ : Submodule R (I ⊗[R] M)) := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · simp
  · intro a m
    change ((a : I) ⊗ₜ[R] m : I ⊗[R] M) ∈
      J • (⊤ : Submodule R (I ⊗[R] M))
    have ha : (a : I) ∈ J • (⊤ : Submodule R I) := hN a.2
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro r hr z _
      simpa [TensorProduct.smul_tmul'] using
        (Submodule.smul_mem_smul hr
          (show z ⊗ₜ[R] m ∈ (⊤ : Submodule R (I ⊗[R] M)) by simp))
    · intro z w hz hw
      simpa [TensorProduct.add_tmul] using add_mem hz hw
  · intro y z hy hz
    simpa [LinearMap.map_add] using add_mem hy hz

/-- Flatness of every positive `I`-power quotient forces the kernel of
`I ⊗[R] M → M` into every stage of the `I`-adic filtration. -/
@[stacks 0523 "ideal-tensor kernel filtration"]
theorem tensorMul_kernel_le_pow_smul_top
    (I : Ideal R) (hflat : Module.Flat.QuotientPowers (M := M) I) (n : ℕ) :
    LinearMap.ker (I.tensorMul M) ≤
      I ^ n • (⊤ : Submodule R (I ⊗[R] M)) := by
  let N : Submodule R I := (I ^ (n + 1)).submoduleOf I
  let Q : Submodule R (I ⊗[R] M) :=
    LinearMap.range (TensorProduct.map N.subtype (LinearMap.id : M →ₗ[R] M))
  let eQuot : (I ⧸ N) ⊗[R] M ≃ₗ[R] (I ⊗[R] M) ⧸ Q :=
    TensorProduct.quotientTensorEquiv M N
  let eStage := idealQuotientTensorStageEquiv (R := R) (M := M) I n
  let stageMul :=
    TensorProduct.lift
      ((LinearMap.lsmul (R ⧸ I ^ (n + 1))
          (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).comp
        (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I).subtype)
  intro x hx
  have hzero :
      stageMul.restrictScalars R
          (eStage (eQuot.symm (Submodule.Quotient.mk x))) = 0 := by
    calc
      stageMul.restrictScalars R
          (eStage (eQuot.symm (Submodule.Quotient.mk x))) =
          idealQuotientTensorMul (R := R) (M := M) I n
            (eQuot.symm (Submodule.Quotient.mk x)) := by
        exact congrArg
          (fun f : (I ⧸ N) ⊗[R] M →ₗ[R]
              M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)) ↦
            f (eQuot.symm (Submodule.Quotient.mk x)))
          (stageTensorMul_comp_stageEquiv (R := R) (M := M) I n)
      _ = (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ (I.tensorMul M x) := by
        exact congrArg
          (fun f : I ⊗[R] M →ₗ[R]
              M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)) ↦ f x)
          (idealQuotientTensorMul_comp_quotientTensorEquiv_symm_mkQ
            (R := R) (M := M) I n)
      _ = 0 := by
        rw [LinearMap.mem_ker.mp hx]
        simp
  have hstageZero : eStage (eQuot.symm (Submodule.Quotient.mk x)) = 0 :=
    (stageTensorMul_injective (R := R) (M := M) I hflat n) (by
      simpa [stageMul] using hzero)
  have hquotZero : Submodule.Quotient.mk x = (0 : (I ⊗[R] M) ⧸ Q) := by
    apply eQuot.symm.injective
    apply eStage.injective
    simpa using hstageZero
  have hxQ : x ∈ Q := (Submodule.Quotient.mk_eq_zero Q).mp hquotZero
  have hN : N ≤ I ^ n • (⊤ : Submodule R I) :=
    (ideal_pow_smul_top_eq_submoduleOf_pow_succ (R := R) I n).ge
  apply range_subtype_rTensor_le_smul_top (R := R) (M := M) I N (I ^ n) hN
  simpa [Q, LinearMap.rTensor_def] using hxQ

section Target

variable {S : Type*} [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [Module S M] [IsScalarTower R S M] [Module.Finite S M]

private noncomputable def sourceTensorMul (I : Ideal R) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) :=
      (TensorProduct.comm R I M).isScalarTower (A := S)
    I ⊗[R] M →ₗ[S] M := by
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) :=
    (TensorProduct.comm R I M).isScalarTower (A := S)
  exact
    (TensorProduct.AlgebraTensorModule.rid R S M).toLinearMap.comp
      ((TensorProduct.AlgebraTensorModule.lTensor S M I.subtype).comp
        ((TensorProduct.comm R I M).toAddEquiv.linearEquiv S).toLinearMap)

omit [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M] in
private lemma sourceTensorMul_restrictScalars (I : Ideal R) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) :=
      (TensorProduct.comm R I M).isScalarTower (A := S)
    (sourceTensorMul (R := R) (S := S) (M := M) I).restrictScalars R = I.tensorMul M := by
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) :=
    (TensorProduct.comm R I M).isScalarTower (A := S)
  apply TensorProduct.ext'
  intro a m
  simp [sourceTensorMul, TensorProduct.AlgebraTensorModule.rid_tmul, Ideal.tensorMul]

omit [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M] in
private lemma sourceTensorMul_kernel_le_mapped_pow
    (I : Ideal R) (hflat : Module.Flat.QuotientPowers (M := M) I) (n : ℕ) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) :=
      (TensorProduct.comm R I M).isScalarTower (A := S)
    LinearMap.ker (sourceTensorMul (R := R) (S := S) (M := M) I) ≤
      (Ideal.map (algebraMap R S) I) ^ n • (⊤ : Submodule S (I ⊗[R] M)) := by
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) :=
    (TensorProduct.comm R I M).isScalarTower (A := S)
  change LinearMap.ker (sourceTensorMul (R := R) (S := S) (M := M) I) ≤
    (Ideal.map (algebraMap R S) I) ^ n • (⊤ : Submodule S (I ⊗[R] M))
  let μ := sourceTensorMul (R := R) (S := S) (M := M) I
  have hkerR :
      LinearMap.ker (μ.restrictScalars R) ≤
        I ^ n • (⊤ : Submodule R (I ⊗[R] M)) := by
    simpa [μ, sourceTensorMul_restrictScalars (R := R) (S := S) (M := M) I] using
      tensorMul_kernel_le_pow_smul_top (R := R) (M := M) I hflat n
  have hpow :
      ((Ideal.map (algebraMap R S) I) ^ n •
          (⊤ : Submodule S (I ⊗[R] M))).restrictScalars R =
        I ^ n • (⊤ : Submodule R (I ⊗[R] M)) := by
    simpa [Ideal.map_pow] using
      (Ideal.smul_restrictScalars
        (R := R) (S := S) (M := I ⊗[R] M) (I := I ^ n)
        (N := (⊤ : Submodule S (I ⊗[R] M))))
  rw [LinearMap.ker_restrictScalars] at hkerR
  intro x hx
  change x ∈ ((Ideal.map (algebraMap R S) I) ^ n •
    (⊤ : Submodule S (I ⊗[R] M))).restrictScalars R
  rw [hpow]
  exact hkerR hx

private lemma sourceTensorMul_localizedKer_eq_bot
    (I : Ideal R) (q : PrimeSpectrum S)
    (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflat : Module.Flat.QuotientPowers (M := M) I) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) :=
      (TensorProduct.comm R I M).isScalarTower (A := S)
    (LinearMap.ker (sourceTensorMul (R := R) (S := S) (M := M) I)).localized
        q.asIdeal.primeCompl = ⊥ := by
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) :=
    (TensorProduct.comm R I M).isScalarTower (A := S)
  change
    (LinearMap.ker (sourceTensorMul (R := R) (S := S) (M := M) I)).localized
      q.asIdeal.primeCompl = ⊥
  letI : Module.Finite R I :=
    ⟨IsNoetherian.noetherian (⊤ : Submodule R I)⟩
  letI : Module.Finite S (M ⊗[R] I) := inferInstance
  let eComm : I ⊗[R] M ≃ₗ[S] M ⊗[R] I :=
    (TensorProduct.comm R I M).toAddEquiv.linearEquiv S
  letI : Module.Finite S (I ⊗[R] M) :=
    Module.Finite.of_surjective eComm.symm.toLinearMap eComm.symm.surjective
  let IS : Ideal S := Ideal.map (algebraMap R S) I
  let K : Submodule S (I ⊗[R] M) :=
    LinearMap.ker (sourceTensorMul (R := R) (S := S) (M := M) I)
  have hK : K ≤ ⨅ n : ℕ, IS ^ n • (⊤ : Submodule S (I ⊗[R] M)) := by
    refine le_iInf fun n ↦ ?_
    simpa [K, IS] using
      sourceTensorMul_kernel_le_mapped_pow
        (R := R) (S := S) (M := M) I hflat n
  have hloc :
      K.localized q.asIdeal.primeCompl ≤
        (⨅ n : ℕ, IS ^ n • (⊤ : Submodule S (I ⊗[R] M))).localized
          q.asIdeal.primeCompl :=
    Submodule.localized_le_localized_of_smul_le q.asIdeal.primeCompl
      ⟨1, Submonoid.one_mem _⟩ (by simpa using hK)
  have hinter :
      (⨅ n : ℕ, IS ^ n • (⊤ : Submodule S (I ⊗[R] M))).localized
          q.asIdeal.primeCompl = ⊥ :=
    Ideal.iInf_pow_smul_localized_eq_bot_of_le IS q.asIdeal hq
  exact le_antisymm (hloc.trans (le_of_eq hinter)) bot_le

private lemma sourceTensorMul_localized_injective
    (I : Ideal R) (q : PrimeSpectrum S)
    (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflat : Module.Flat.QuotientPowers (M := M) I) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) :=
      (TensorProduct.comm R I M).isScalarTower (A := S)
    Function.Injective
      (LocalizedModule.map q.asIdeal.primeCompl
        (sourceTensorMul (R := R) (S := S) (M := M) I)) := by
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) :=
    (TensorProduct.comm R I M).isScalarTower (A := S)
  change Function.Injective
    (LocalizedModule.map q.asIdeal.primeCompl
      (sourceTensorMul (R := R) (S := S) (M := M) I))
  have hker :
      LinearMap.ker
          (LocalizedModule.map q.asIdeal.primeCompl
            (sourceTensorMul (R := R) (S := S) (M := M) I)) = ⊥ := by
    rw [← LinearMap.localizedKer_eq_ker_map]
    exact sourceTensorMul_localizedKer_eq_bot
      (R := R) (S := S) (M := M) I q hq hflat
  intro x y hxy
  have hmem :
      x - y ∈ LinearMap.ker
        (LocalizedModule.map q.asIdeal.primeCompl
          (sourceTensorMul (R := R) (S := S) (M := M) I)) := by
    rw [LinearMap.mem_ker]
    simpa using congrArg (fun z ↦ z -
      LocalizedModule.map q.asIdeal.primeCompl
        (sourceTensorMul (R := R) (S := S) (M := M) I) y) hxy
  rw [hker] at hmem
  exact sub_eq_zero.mp hmem

private noncomputable def localizedSourceTensorEquiv
    (I : Ideal R) (q : PrimeSpectrum S) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) :=
      (TensorProduct.comm R I M).isScalarTower (A := S)
    let Mq := LocalizedModule.AtPrime q.asIdeal M
    let _ : Module S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] Mq) :=
      (TensorProduct.comm R I Mq).isScalarTower (A := S)
    LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[S] I ⊗[R] Mq := by
  let Mq := LocalizedModule.AtPrime q.asIdeal M
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) :=
    (TensorProduct.comm R I M).isScalarTower (A := S)
  letI : Module S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] Mq) :=
    (TensorProduct.comm R I Mq).isScalarTower (A := S)
  let eComm :
      LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[S]
        LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    LocalizedModule.AtPrime.mapEquiv q.asIdeal
      ((TensorProduct.comm R I M).toAddEquiv.linearEquiv S)
  let eTensor :
      Mq ⊗[R] I ≃ₗ[S] LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    LocalizedModule.tensorRightLinearEquiv
      (R := R) (A := S) (X := M) q.asIdeal.primeCompl I
  let eCommTarget : I ⊗[R] Mq ≃ₗ[S] Mq ⊗[R] I :=
    (TensorProduct.comm R I Mq).toAddEquiv.linearEquiv S
  exact eComm.trans (eTensor.symm.trans eCommTarget.symm)

omit [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M] in
@[simp] private theorem localizedSourceTensorEquiv_apply_mk_tmul
    (I : Ideal R) (q : PrimeSpectrum S) (a : I) (m : M) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) :=
      (TensorProduct.comm R I M).isScalarTower (A := S)
    let Mq := LocalizedModule.AtPrime q.asIdeal M
    let _ : Module S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] Mq) :=
      (TensorProduct.comm R I Mq).isScalarTower (A := S)
    localizedSourceTensorEquiv (R := R) (S := S) (M := M) I q
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M) (a ⊗ₜ[R] m)) =
      a ⊗ₜ[R] LocalizedModule.mkLinearMap q.asIdeal.primeCompl M m := by
  let Mq := LocalizedModule.AtPrime q.asIdeal M
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) :=
    (TensorProduct.comm R I M).isScalarTower (A := S)
  letI : Module S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] Mq) :=
    (TensorProduct.comm R I Mq).isScalarTower (A := S)
  let eComm :
      LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[S]
        LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    LocalizedModule.AtPrime.mapEquiv q.asIdeal
      ((TensorProduct.comm R I M).toAddEquiv.linearEquiv S)
  let eTensor :
      Mq ⊗[R] I ≃ₗ[S] LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    LocalizedModule.tensorRightLinearEquiv
      (R := R) (A := S) (X := M) q.asIdeal.primeCompl I
  have hComm :
      eComm (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M)
          (a ⊗ₜ[R] m)) =
        LocalizedModule.mkLinearMap q.asIdeal.primeCompl (M ⊗[R] I)
          (m ⊗ₜ[R] a) := by
    simpa [eComm] using
      (LocalizedModule.AtPrime.mapEquiv_apply_mk q.asIdeal
        ((TensorProduct.comm R I M).toAddEquiv.linearEquiv S) (a ⊗ₜ[R] m))
  have hTensor :
      eTensor.symm
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (M ⊗[R] I)
            (m ⊗ₜ[R] a)) =
        LocalizedModule.mkLinearMap q.asIdeal.primeCompl M m ⊗ₜ[R] a := by
    simpa [eTensor, LocalizedModule.tensorRightLinearEquiv] using
      (IsLocalizedModule.linearEquiv_symm_apply
        (S := q.asIdeal.primeCompl)
        (f := TensorProduct.AlgebraTensorModule.rTensor R I
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M))
        (g := LocalizedModule.mkLinearMap q.asIdeal.primeCompl (M ⊗[R] I))
        (x := m ⊗ₜ[R] a))
  rw [localizedSourceTensorEquiv]
  simp only [LinearEquiv.trans_apply]
  rw [hComm, hTensor]
  simp

omit [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M] in
private lemma sourceTensorMul_localized_conjugation
    (I : Ideal R) (q : PrimeSpectrum S) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) :=
      (TensorProduct.comm R I M).isScalarTower (A := S)
    let Mq := LocalizedModule.AtPrime q.asIdeal M
    let _ : Module S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] Mq) :=
      (TensorProduct.comm R I Mq).isScalarTower (A := S)
    (sourceTensorMul (R := R) (S := S) (M := Mq) I).comp
        (localizedSourceTensorEquiv (R := R) (S := S) (M := M) I q).toLinearMap =
      LocalizedModule.map q.asIdeal.primeCompl
        (sourceTensorMul (R := R) (S := S) (M := M) I) := by
  let Mq := LocalizedModule.AtPrime q.asIdeal M
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) :=
    (TensorProduct.comm R I M).isScalarTower (A := S)
  letI : Module S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] Mq) :=
    (TensorProduct.comm R I Mq).isScalarTower (A := S)
  apply IsLocalizedModule.linearMap_ext q.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M))
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
  apply LinearMap.restrictScalars_injective R
  apply TensorProduct.ext'
  intro a m
  change
    sourceTensorMul (R := R) (S := S) (M := Mq) I
        (localizedSourceTensorEquiv (R := R) (S := S) (M := M) I q
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M)
            (a ⊗ₜ[R] m))) =
      LocalizedModule.map q.asIdeal.primeCompl
          (sourceTensorMul (R := R) (S := S) (M := M) I)
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M)
          (a ⊗ₜ[R] m))
  rw [localizedSourceTensorEquiv_apply_mk_tmul]
  rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply]
  rw [LocalizedModule.map_mk]
  simp [sourceTensorMul, TensorProduct.AlgebraTensorModule.rid_tmul]
  simpa using
    (LocalizedModule.smul'_mk (S := q.asIdeal.primeCompl)
      (r := algebraMap R S (a : R)) (s := 1) (m := m))

/-- Ideal tensor multiplication remains injective after localizing the target module at a prime
containing the extended ideal. -/
@[stacks 0523 "prime-local ideal-tensor injectivity"]
theorem tensorMul_localizedModule_atPrime_injective
    (I : Ideal R) (q : PrimeSpectrum S)
    (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflat : Module.Flat.QuotientPowers (M := M) I) :
    Function.Injective (I.tensorMul (LocalizedModule.AtPrime q.asIdeal M)) := by
  let Mq := LocalizedModule.AtPrime q.asIdeal M
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) :=
    (TensorProduct.comm R I M).isScalarTower (A := S)
  letI : Module S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] Mq) :=
    (TensorProduct.comm R I Mq).isScalarTower (A := S)
  let e := localizedSourceTensorEquiv (R := R) (S := S) (M := M) I q
  let μ := sourceTensorMul (R := R) (S := S) (M := Mq) I
  let f := LocalizedModule.map q.asIdeal.primeCompl
    (sourceTensorMul (R := R) (S := S) (M := M) I)
  have hf : Function.Injective f := by
    simpa [f] using sourceTensorMul_localized_injective
      (R := R) (S := S) (M := M) I q hq hflat
  have hcompare : μ.comp e.toLinearMap = f := by
    simpa [e, μ, f] using
      sourceTensorMul_localized_conjugation (R := R) (S := S) (M := M) I q
  have hμ : Function.Injective μ := by
    intro x y hxy
    have hcomp :
        (μ.comp e.toLinearMap) (e.symm x) =
          (μ.comp e.toLinearMap) (e.symm y) := by
      simpa using hxy
    rw [hcompare] at hcomp
    have heq := hf hcomp
    simpa using congrArg e heq
  have hrestrict : μ.restrictScalars R = I.tensorMul Mq := by
    simpa [μ] using
      sourceTensorMul_restrictScalars (R := R) (S := S) (M := Mq) I
  rw [← hrestrict]
  exact hμ

/-- After passing to the local base ring at the contracted prime, multiplication by the extended
ideal remains injective on the localized target module.  The relative module action is kept local
to the statement and proof. -/
@[stacks 0523 "extended ideal-tensor injectivity at a prime"]
theorem tensorMul_atPrime_injective
    (I : Ideal R) (q : PrimeSpectrum S)
    (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflat : Module.Flat.QuotientPowers (M := M) I) :
    let p := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let Mq := LocalizedModule.AtPrime q.asIdeal M
    letI : Module Rp Mq :=
      Localization.AtPrime.Relative.algebraMapModule (R := R) q.asIdeal
    letI : IsScalarTower R Rp Mq :=
      Localization.AtPrime.Relative.algebraMapModule_isScalarTower
        (R := R) (S := S) (M := M) q.asIdeal
    Function.Injective ((Ideal.map (algebraMap R Rp) I).tensorMul Mq) := by
  let p := q.asIdeal.under R
  let Rp := Localization.AtPrime p
  let Mq := LocalizedModule.AtPrime q.asIdeal M
  letI : Module Rp Mq :=
    Localization.AtPrime.Relative.algebraMapModule (R := R) q.asIdeal
  letI : IsScalarTower R Rp Mq :=
    Localization.AtPrime.Relative.algebraMapModule_isScalarTower
      (R := R) (S := S) (M := M) q.asIdeal
  exact Ideal.Map.tensorMul_injective (S := Rp) (M := Mq) I
    (tensorMul_localizedModule_atPrime_injective
      (R := R) (S := S) (M := M) I q hq hflat)

end Target

end Module.Flat.QuotientPowers
