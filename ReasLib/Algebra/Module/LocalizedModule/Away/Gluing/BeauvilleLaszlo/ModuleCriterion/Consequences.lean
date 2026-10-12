/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
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
          (algebraMap R (principalAdicCompletion f)) (principalIdeal f) M) := sorry

/-- Remark 15.91.11 (1): for the completion glueing pair, `M` is glueable exactly when its
power-torsion comparison to the full completion tensor product is injective. -/
@[stacks 0BNX "Remark 15.91.11 (1)"]
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToCompletionTensor
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f)) f) :
    (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact ↔
      Function.Injective (completionFPowerTorsionToCompletionTensor M f) := sorry

/-- A nonzero power-torsion element in the kernel of the completion-tensor comparison obstructs
glueability. -/
theorem not_glueable_along_principalAdicCompletion_of_nonzero_completionTensor_kernel
    (f : R) {x : (principalIdeal f).primaryComponent M} (hx_ne : x ≠ 0)
    (hcompletion : completionFPowerTorsionToCompletionTensor M f x = 0) :
    ¬ (beauvilleLaszloModuleCechSequence
      (principalAdicCompletion f) M f).ShortExact := sorry

/-- Remark 15.91.11 (1), sufficient condition: injectivity on the submodule killed by `f`
implies module glueability along the completion glueing pair. -/
@[stacks 0BNX "Remark 15.91.11 (1), sufficient condition"]
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_of_injective_fTorsionToAdicCompletion
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f)) f)
    (hinj : Function.Injective (fTorsionToAdicCompletion M f)) :
    (beauvilleLaszloModuleCechSequence
      (principalAdicCompletion f) M f).ShortExact := sorry

/-- Remark 15.91.11 (1), intersection criterion: injectivity on `f`-torsion is equivalent to
trivial intersection with all positive principal powers. -/
@[stacks 0BNX "Remark 15.91.11 (1), intersection criterion"]
theorem fTorsionToAdicCompletion_injective_iff_torsion_inf_principalPowers_eq_bot
    (f : R) :
    Function.Injective (fTorsionToAdicCompletion M f) ↔
      Submodule.torsionBy R M f ⊓
          ⨅ n : ℕ+, principalPowerIdeal f (n : ℕ) • (⊤ : Submodule R M) =
        ⊥ := sorry

/-- Remark 15.91.11 (2): vanishing of first Tor against the localized target implies module
glueability for a Beauville-Laszlo glueing pair. -/
@[stacks 0BNX "Remark 15.91.11 (2)"]
theorem isBeauvilleLaszloGlueableAlong_of_torOne_localizedTarget_isZero
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (hTor : IsZero
      (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
        (ModuleCat.of R (Localization.Away (algebraMap R R' f))))) :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact := sorry

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
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact := sorry

/-- Remark 15.91.11 (3): if the extension is flat, every module is glueable for a
Beauville-Laszlo glueing pair. -/
@[stacks 0BNX "Remark 15.91.11 (3)"]
theorem isBeauvilleLaszloGlueableAlong_of_flat_extension
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    [Module.Flat R R'] :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact := sorry

/-- Remark 15.91.11 (3), Noetherian specialization: over a Noetherian ring, every module is
glueable along the principal-adic completion. -/
@[stacks 0BNX "Remark 15.91.11 (3), Noetherian specialization"]
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_of_isNoetherianRing
    (f : R) [IsNoetherianRing R] :
    (beauvilleLaszloModuleCechSequence
      (principalAdicCompletion f) M f).ShortExact := sorry

end
