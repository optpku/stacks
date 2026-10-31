/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import ReasLib.Algebra.Category.ModuleCat.Tor.Exact
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Flat
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCriterion

import Mathlib.Tactic.CrossRefAttribute

/-!
# Consequences of the module Beauville-Laszlo criterion

Completion-separatedness, first-Tor vanishing, and flatness give practical sufficient conditions
for module glueability.

@stack 0BNX
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- The comparison from the `f`-power-torsion submodule of `M` to the full tensor product with
the principal-adic completion. -/
@[stacks 0BNX "comparison from completed f-power torsion to completed tensor product"]
noncomputable abbrev completionFPowerTorsionToCompletionTensor (M : Type u)
    [AddCommGroup M] [Module R M] (f : R) :
    (principalIdeal f).primaryComponent M →ₗ[R] M ⊗[R] principalAdicCompletion f :=
  let A := principalAdicCompletion f
  let targetTorsion : Submodule R (A ⊗[R] M) :=
    ((Ideal.map (algebraMap R A) (principalIdeal f)).primaryComponent
      (A ⊗[R] M)).restrictScalars R
  let η : (principalIdeal f).primaryComponent M →ₗ[R] targetTorsion :=
    Ideal.primaryComponent.baseChangeUnit
      (algebraMap R A) (principalIdeal f) M
  (TensorProduct.comm R A M).toLinearMap.comp (targetTorsion.subtype.comp η)

/-- The restriction of the adic-completion map to the submodule killed by `f`. -/
@[stacks 0BNX "comparison from f-torsion to adic completion"]
noncomputable abbrev fTorsionToAdicCompletion (M : Type u)
    [AddCommGroup M] [Module R M] (f : R) :
    Submodule.torsionBy R M f →ₗ[R] AdicCompletion (principalIdeal f) M :=
  (AdicCompletion.of (principalIdeal f) M).domRestrict (Submodule.torsionBy R M f)

/-- Injectivity of the full completion-tensor map is equivalent to injectivity of the canonical
base-change map on the primary component. -/
theorem completionFPowerTorsionToCompletionTensor_injective_iff (f : R) :
    Function.Injective (completionFPowerTorsionToCompletionTensor M f) ↔
      Function.Injective
        (Ideal.primaryComponent.baseChangeUnit
          (algebraMap R (principalAdicCompletion f)) (principalIdeal f) M) := by
  let A := principalAdicCompletion f
  let targetTorsion : Submodule R (A ⊗[R] M) :=
    ((Ideal.map (algebraMap R A) (principalIdeal f)).primaryComponent
      (A ⊗[R] M)).restrictScalars R
  let η : (principalIdeal f).primaryComponent M →ₗ[R] targetTorsion :=
    Ideal.primaryComponent.baseChangeUnit
      (algebraMap R A) (principalIdeal f) M
  change Function.Injective ((TensorProduct.comm R A M).toLinearMap.comp
      (targetTorsion.subtype.comp η)) ↔ Function.Injective η
  constructor
  · intro h x y hxy
    apply h
    simpa only [LinearMap.coe_comp, Function.comp_apply] using
      congrArg (fun z => (TensorProduct.comm R A M).toLinearMap z)
        (congrArg (fun z => targetTorsion.subtype z) hxy)
  · intro h x y hxy
    apply h
    apply Subtype.ext
    apply (TensorProduct.comm R A M).injective
    exact hxy

/-- Remark 15.91.11 (1): for the completion glueing pair, `M` is glueable exactly when its
power-torsion comparison to the full completion tensor product is injective. -/
@[stacks 0BNX "Remark 15.91.11 (1)"]
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToCompletionTensor
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f)) f) :
    (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact ↔
      Function.Injective (completionFPowerTorsionToCompletionTensor M f) := by
  rw [completionFPowerTorsionToCompletionTensor_injective_iff]
  exact isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToTensor_of_glueingPair
    f hpair

/-- A nonzero power-torsion element in the kernel of the completion-tensor comparison obstructs
glueability. -/
theorem not_glueable_along_principalAdicCompletion_of_nonzero_completionTensor_kernel
    (f : R) {x : (principalIdeal f).primaryComponent M} (hx_ne : x ≠ 0)
    (hcompletion : completionFPowerTorsionToCompletionTensor M f x = 0) :
    ¬ (beauvilleLaszloModuleCechSequence
      (principalAdicCompletion f) M f).ShortExact := by
  intro hshort
  have hleft : Function.Injective
      ((beauvilleLaszloModuleCechSequence
        (principalAdicCompletion f) M f).f.hom) := hshort.moduleCat_injective_f
  have hbase : Function.Injective
      (Ideal.primaryComponent.baseChangeUnit
        (algebraMap R (principalAdicCompletion f)) (principalIdeal f) M) :=
    (beauvilleLaszloModuleCechLeftMap_injective_iff_fPowerTorsionToTensor_injective
      (R' := principalAdicCompletion f) f).mp hleft
  have hinj : Function.Injective (completionFPowerTorsionToCompletionTensor M f) :=
    (completionFPowerTorsionToCompletionTensor_injective_iff (M := M) f).mpr hbase
  exact hx_ne (hinj (by simpa [hcompletion]))

/-- Remark 15.91.11 (1), sufficient condition: injectivity on the submodule killed by `f`
implies module glueability along the completion glueing pair. -/
@[stacks 0BNX "Remark 15.91.11 (1), sufficient condition"]
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_of_injective_fTorsionToAdicCompletion
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f)) f)
    (hinj : Function.Injective (fTorsionToAdicCompletion M f)) :
    (beauvilleLaszloModuleCechSequence
      (principalAdicCompletion f) M f).ShortExact := by
  have hzero : ∀ n : ℕ, ∀ x : M, f ^ n • x = 0 →
      AdicCompletion.of (principalIdeal f) M x = 0 → x = 0 := by
    intro n
    induction n with
    | zero =>
      intro x hx _
      simpa using hx
    | succ n ih =>
      intro x hx hcompletion
      have hfx : f • x = 0 := ih (f • x)
        (by simpa [pow_succ, mul_smul] using hx)
        (by simp [hcompletion])
      have hx' : (⟨x, hfx⟩ : Submodule.torsionBy R M f) = 0 :=
        hinj (by simpa [fTorsionToAdicCompletion] using hcompletion)
      exact congrArg Subtype.val hx'
  apply (isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToTensor_of_glueingPair
    f hpair).mpr
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  change (x : M) = 0
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M (principalIdeal f) (x : M)).mp x.property
  apply hzero n (x : M)
  · exact (Submodule.mem_torsionBySet_iff _ _).mp hn
      ⟨f ^ n, Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton f)) n⟩
  · have htensor : (1 : principalAdicCompletion f) ⊗ₜ[R] (x : M) = 0 :=
      congrArg Subtype.val hx
    have hcompletion := congrArg (AdicCompletion.ofTensorProduct (principalIdeal f) M) htensor
    simpa using hcompletion

/-- Remark 15.91.11 (1), intersection criterion: injectivity on `f`-torsion is equivalent to
trivial intersection with all positive principal powers. -/
@[stacks 0BNX "Remark 15.91.11 (1), intersection criterion"]
theorem fTorsionToAdicCompletion_injective_iff_torsion_inf_principalPowers_eq_bot
    (f : R) :
    Function.Injective (fTorsionToAdicCompletion M f) ↔
      Submodule.torsionBy R M f ⊓
          ⨅ n : ℕ+, principalPowerIdeal f (n : ℕ) • (⊤ : Submodule R M) =
        ⊥ := by
  have hker : (AdicCompletion.of (principalIdeal f) M).ker =
      ⨅ n : ℕ+, principalPowerIdeal f (n : ℕ) • (⊤ : Submodule R M) := by
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      apply (Submodule.mem_iInf _).mpr
      intro n
      have hn := congrArg (AdicCompletion.eval (principalIdeal f) M (n : ℕ)) hx
      simpa [AdicCompletion.eval_of] using hn
    · intro hx
      apply AdicCompletion.ext
      intro n
      cases n with
      | zero => simp [AdicCompletion.of_apply]
      | succ n =>
        have hn := (Submodule.mem_iInf _).mp hx ⟨n + 1, Nat.succ_pos n⟩
        simpa [AdicCompletion.of_apply] using hn
  rw [fTorsionToAdicCompletion, LinearMap.injective_domRestrict_iff,
    disjoint_iff, hker]

private theorem moduleCech_shortExact_of_tensorImage_shortExact (f : R)
    (hT : (beauvilleLaszloModuleCechTensorImage R' M f).ShortExact) :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact := by
  let T := beauvilleLaszloModuleCechTensorImage R' M f
  apply ShortComplex.shortExact_of_iso ?_ hT
  refine ShortComplex.isoMk
    (beauvilleLaszloModuleCechLeftIso R' M f)
    (beauvilleLaszloModuleCechMiddleIso R' M f)
    (Iso.refl T.X₃) ?_ ?_
  · change (beauvilleLaszloModuleCechLeftIso R' M f).hom ≫
        (beauvilleLaszloModuleCechLeftIso R' M f).inv ≫ T.f ≫
          (beauvilleLaszloModuleCechMiddleIso R' M f).hom =
      T.f ≫ (beauvilleLaszloModuleCechMiddleIso R' M f).hom
    rw [Iso.hom_inv_id_assoc]
  · change (beauvilleLaszloModuleCechMiddleIso R' M f).hom ≫
        (beauvilleLaszloModuleCechMiddleIso R' M f).inv ≫ T.g = T.g ≫ 𝟙 _
    rw [Iso.hom_inv_id_assoc, Category.comp_id]

/-- Remark 15.91.11 (2): vanishing of first Tor against the localized target implies module
glueability for a Beauville-Laszlo glueing pair. -/
@[stacks 0BNX "Remark 15.91.11 (2)"]
theorem isBeauvilleLaszloGlueableAlong_of_torOne_localizedTarget_isZero
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (hTor : IsZero
      (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
        (ModuleCat.of R (Localization.Away (algebraMap R R' f))))) :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact := by
  let S := beauvilleLaszloCechSequence (algebraMap R R') f
  have hS : S.ShortExact := hpair.shortExact
  have hX₃ : S.X₃ = ModuleCat.of R (Localization.Away (algebraMap R R' f)) := by
    exact congrArg (fun a : Algebra R R' =>
      letI := a
      ModuleCat.of R (Localization.Away (algebraMap R R' f)))
      (toAlgebra_algebraMap (R := R) (S := R'))
  have hTor' : IsZero (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₃) := by
    rw [hX₃]
    exact hTor
  obtain ⟨δ, _, hδ⟩ := ModuleCat.Tor.exists_lTensorBoundary_exact M S.f.hom S.g.hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
    hS.moduleCat_injective_f hS.moduleCat_surjective_g
  have hδzero : δ = 0 := hTor'.eq_of_src δ 0
  have hinj : Function.Injective (S.f.hom.lTensor M) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.exact_iff.mp hδ, hδzero]
    simp
  apply moduleCech_shortExact_of_tensorImage_shortExact
  apply ModuleCat.shortComplex_shortExact
  · exact lTensor_exact M
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
      hS.moduleCat_surjective_g
  · exact hinj
  · exact LinearMap.lTensor_surjective M hS.moduleCat_surjective_g

/-- Remark 15.91.11 (2), equivalent condition: first Tor against `R'` is power torsion exactly
when first Tor against the localization of `R'` away from `f` vanishes. -/
@[stacks 0BNX "Remark 15.91.11 (2), equivalent condition"]
theorem torOne_extension_isTorsion'_powers_iff_torOne_localizedTarget_isZero
    (f : R) :
    Module.IsTorsion'
        (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
          (ModuleCat.of R R'))
        (Submonoid.powers f) ↔
      IsZero
        (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
          (ModuleCat.of R (Localization.Away (algebraMap R R' f)))) := sorry

/-- Remark 15.91.11 (2), flat special case: every flat module is glueable for a
Beauville-Laszlo glueing pair. -/
@[stacks 0BNX "Remark 15.91.11 (2), flat special case"]
theorem isBeauvilleLaszloGlueableAlong_of_flat_module
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    [Module.Flat R M] :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact := by
  apply moduleCech_shortExact_of_tensorImage_shortExact
  apply ModuleCat.shortComplex_shortExact
  · exact Module.Flat.lTensor_exact M
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hpair.shortExact.exact)
  · exact Module.Flat.lTensor_preserves_injective_linearMap
      (beauvilleLaszloCechSequence (algebraMap R R') f).f.hom
      hpair.shortExact.moduleCat_injective_f
  · exact LinearMap.lTensor_surjective M hpair.shortExact.moduleCat_surjective_g

/-- Remark 15.91.11 (3): if the extension is flat, every module is glueable for a
Beauville-Laszlo glueing pair. -/
@[stacks 0BNX "Remark 15.91.11 (3)"]
theorem isBeauvilleLaszloGlueableAlong_of_flat_extension
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    [Module.Flat R R'] :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact := by
  apply (isBeauvilleLaszloGlueableAlong_iff_bijective_fPowerTorsionToTensor
    f hpair.quotientMapBijective).mpr
  apply Ideal.primaryComponent.baseChangeUnit_bijective
    (algebraMap R R') (principalIdeal f) M (Submodule.fg_span_singleton f)
  · exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · have hmap : (principalIdeal f).map (algebraMap R R') =
        principalIdeal (algebraMap R R' f) := by
      simp [principalIdeal, Ideal.map_span]
    let e₁ : R ⧸ principalIdeal f ≃+* R ⧸ principalPowerIdeal f 1 :=
      Ideal.quotEquivOfEq (pow_one (principalIdeal f)).symm
    let e₂ : R' ⧸ principalPowerIdeal (algebraMap R R' f) 1 ≃+*
        R' ⧸ (principalIdeal f).map (algebraMap R R') :=
      Ideal.quotEquivOfEq ((pow_one _).trans hmap.symm)
    have hcomp : e₂.toRingHom.comp
        ((principalPowerIdealImageQuotientMap (algebraMap R R') f 1).comp e₁.toRingHom) =
          (algebraMap R R').quotientByIdeal (principalIdeal f) := by
      ext x
      rfl
    rw [← hcomp]
    exact e₂.bijective.comp ((hpair.quotientMapBijective 1).comp e₁.bijective)

/-- Remark 15.91.11 (3), Noetherian specialization: over a Noetherian ring, every module is
glueable along the principal-adic completion. -/
@[stacks 0BNX "Remark 15.91.11 (3), Noetherian specialization"]
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_of_isNoetherianRing
    (f : R) [IsNoetherianRing R] :
    (beauvilleLaszloModuleCechSequence
      (principalAdicCompletion f) M f).ShortExact := by
  exact isBeauvilleLaszloGlueableAlong_of_flat_extension f
    (LocalizedModule.Away.BeauvilleLaszlo.principalAdicCompletion_isGlueingPair_of_isNoetherianRing f)

end
