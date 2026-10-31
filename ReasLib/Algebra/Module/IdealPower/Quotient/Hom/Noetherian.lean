/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Module.IdealPower.Quotient.Hom.Completion
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom systems over ideal-power quotients of finite modules

@stack 09BB

For finite modules over a Noetherian ring, the positive ideal-power Hom system is
Mittag-Leffler and is compared to the adic completion of the linear-map module.  The
completion-to-limit morphism is exposed independently of the finiteness hypotheses so that
downstream results can refer to the canonical map, rather than only to an unspecified
isomorphism of its source and target.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v w

namespace Ideal.PowerQuotient.Hom

variable {R : Type u} [CommRing R]

/-- The canonical comparison from the adic completion of `Hom_R(M, N)` to the inverse limit of
the positive ideal-power Hom system. -/
@[stacks 09BB "completion-to-limit comparison for the ideal-power Hom system"]
noncomputable def limitComparison
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    ModuleCat.of R (AdicCompletion I (M →ₗ[R] N)) ⟶ limit (system I M N) :=
  (positiveLimitIso I (ModuleCat.of R (M →ₗ[R] N))).inv ≫
    lim.map (comparisonNatTrans I M N)

/-- Projecting `limitComparison` to stage `n` first evaluates the adic completion modulo
`I ^ (n + 1)` and then applies the stagewise quotient-Hom comparison. -/
@[stacks 09BB "projection formula for the completion-to-Hom-limit comparison"]
theorem limitComparison_comp_π
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    limitComparison I M N ≫ limit.π (system I M N) (op n) =
      ModuleCat.ofHom (AdicCompletion.eval I (M →ₗ[R] N) (n + 1)) ≫
        comparisonApp I M N n := by
  unfold limitComparison
  rw [Category.assoc, ← limMap_eq, limMap_π, ← Category.assoc, positiveLimitIso_inv_comp_π,
    comparisonNatTrans_app]
  rfl

/-- The source-facing completion comparison whose target is the inverse limit of
`Hom_R(M / I ^ (n + 1) M, N / I ^ (n + 1) N)`. -/
@[stacks 09BB "completion-to-quotient-domain Hom-limit comparison"]
noncomputable def quotientLimitComparison
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    ModuleCat.of R (AdicCompletion I (M →ₗ[R] N)) ⟶
      limit (quotientSystem I M N) :=
  limitComparison I M N ≫ lim.map (quotientSystemIso I M N).inv

/-- Projection of the source-facing completion comparison to a quotient-domain Hom stage. -/
@[stacks 09BB "projection formula for the quotient-domain Hom-limit comparison"]
theorem quotientLimitComparison_comp_π
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    quotientLimitComparison I M N ≫ limit.π (quotientSystem I M N) (op n) =
      ModuleCat.ofHom (AdicCompletion.eval I (M →ₗ[R] N) (n + 1)) ≫
        comparisonApp I M N n ≫
          (quotientSystemIso I M N).inv.app (op n) := by
  unfold quotientLimitComparison
  rw [Category.assoc, ← limMap_eq, limMap_π, ← Category.assoc, limitComparison_comp_π,
    Category.assoc]

variable [IsNoetherianRing R]

/-- Lemma 15.101.4 (1) (09BB): the source-facing system of Hom modules between positive
ideal-power quotients is Mittag-Leffler for finite modules over a Noetherian ring. -/
@[stacks 09BB "Mittag-Leffler property for Hom between quotient stages"]
theorem quotientSystem_isMittagLeffler
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    (quotientSystem I M N).IsMittagLeffler := sorry

/-- Lemma 15.101.4 (1) (09BB): for finite `R`-modules `M` and `N`, the inverse system
`n ↦ Hom_R(M, N / I ^ (n + 1) N)` is Mittag-Leffler. -/
@[stacks 09BB "Mittag-Leffler property for Hom over ideal-power quotients"]
theorem system_isMittagLeffler
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    (system I M N).IsMittagLeffler := by
  let e := quotientSystemIso I M N
  intro i
  obtain ⟨c, hic, hc⟩ := quotientSystem_isMittagLeffler I M N i
  have himage {j : ℕ} (hij : i ≤ j) :
      imageSubobject ((system I M N).transitionMap hij) =
        (Subobject.map (e.hom.app (op i))).obj
          (imageSubobject ((quotientSystem I M N).transitionMap hij)) := by
    calc
      imageSubobject ((system I M N).transitionMap hij) =
          imageSubobject (e.hom.app (op j) ≫ (system I M N).transitionMap hij) :=
        (imageSubobject_iso_comp _ _).symm
      _ = imageSubobject ((quotientSystem I M N).transitionMap hij ≫
          e.hom.app (op i)) :=
        congrArg (fun f : (quotientSystem I M N).obj (op j) ⟶
            (system I M N).obj (op i) ↦ imageSubobject f)
          (e.hom.naturality (homOfLE hij).op).symm
      _ = _ := by
        change Subobject.mk (image.ι _) =
          Subobject.mk (image.ι ((quotientSystem I M N).transitionMap hij) ≫
            e.hom.app (op i))
        exact (Subobject.mk_eq_mk_of_comm _ _ (image.compIso _ _)
          (image.compIso_hom_comp_image_ι _ _)).symm
  refine ⟨c, hic, fun {k} hck ↦ ?_⟩
  rw [himage, himage]
  exact congrArg (Subobject.map (e.hom.app (op i))).obj (hc hck)

/-- Lemma 15.101.4 (2) (09BB): one power `I ^ c` annihilates the kernel and cokernel
of every stage of the quotient-Hom comparison. -/
@[stacks 09BB "uniform annihilation for the quotient Hom comparison"]
theorem exists_comparison_kernel_cokernel_annihilation
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    ∃ c : ℕ, ∀ n : ℕ,
      I ^ c • (⊤ : Submodule R (LinearMap.ker (comparison I M N n))) = ⊥ ∧
        I ^ c •
            (⊤ : Submodule R
              (stage I M N n ⧸ LinearMap.range (comparison I M N n))) =
          ⊥ := sorry

/-- A positive-exponent form of the uniform kernel/cokernel annihilation theorem. -/
@[stacks 09BB "positive uniform annihilation for the quotient Hom comparison"]
theorem exists_comparison_kernel_cokernel_annihilation_pos
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ,
      I ^ c • (⊤ : Submodule R (LinearMap.ker (comparison I M N n))) = ⊥ ∧
        I ^ c •
            (⊤ : Submodule R
              (stage I M N n ⧸ LinearMap.range (comparison I M N n))) =
          ⊥ := by
  obtain ⟨c, hc⟩ := exists_comparison_kernel_cokernel_annihilation I M N
  refine ⟨c + 1, Nat.succ_pos c, fun n ↦ ⟨?_, ?_⟩⟩
  · apply eq_bot_iff.mpr
    calc
      I ^ (c + 1) • ⊤ ≤ I ^ c • ⊤ :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ c))
      _ = ⊥ := (hc n).1
  · apply eq_bot_iff.mpr
    calc
      I ^ (c + 1) • ⊤ ≤ I ^ c • ⊤ :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ c))
      _ = ⊥ := (hc n).2

/-- Lemma 15.101.4 (2) (09BB): the same uniform annihilation statement for the source-facing
comparison into `Hom_R(M / I ^ (n + 1) M, N / I ^ (n + 1) N)`. -/
@[stacks 09BB "uniform annihilation for the quotient-domain Hom comparison"]
theorem exists_quotientComparison_kernel_cokernel_annihilation
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    ∃ c : ℕ, ∀ n : ℕ,
      I ^ c • (⊤ : Submodule R (LinearMap.ker (quotientComparison I M N n))) = ⊥ ∧
        I ^ c •
            (⊤ : Submodule R
              (quotientStage I M N n ⧸ LinearMap.range (quotientComparison I M N n))) =
          ⊥ := by
  obtain ⟨c, hc⟩ := exists_comparison_kernel_cokernel_annihilation I M N
  refine ⟨c, fun n ↦ ⟨?_, ?_⟩⟩
  · have hker : LinearMap.ker (quotientComparison I M N n) =
        LinearMap.ker (comparison I M N n) := by
      ext x
      simp [quotientComparison]
    rw [hker]
    exact (hc n).1
  · let e := (quotientStageEquiv I M N n).symm
    have he : (LinearMap.range (comparison I M N n)).map e.toLinearMap =
        LinearMap.range (quotientComparison I M N n) := by
      rw [← LinearMap.range_comp]
      rfl
    let eQ := Submodule.Quotient.equiv _ _ e he
    have htop : (⊤ : Submodule R
        (stage I M N n ⧸ LinearMap.range (comparison I M N n))).map eQ.toLinearMap = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top.mpr eQ.surjective]
    have h := congrArg (Submodule.map eQ.toLinearMap) (hc n).2
    simpa only [Submodule.map_smul'', htop, Submodule.map_bot] using h

/-- A positive-exponent form of the source-facing quotient-domain annihilation theorem. -/
@[stacks 09BB "positive uniform annihilation for the quotient-domain Hom comparison"]
theorem exists_quotientComparison_kernel_cokernel_annihilation_pos
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ,
      I ^ c • (⊤ : Submodule R (LinearMap.ker (quotientComparison I M N n))) = ⊥ ∧
        I ^ c •
            (⊤ : Submodule R
              (quotientStage I M N n ⧸ LinearMap.range (quotientComparison I M N n))) =
          ⊥ := by
  obtain ⟨c, hc⟩ := exists_quotientComparison_kernel_cokernel_annihilation I M N
  refine ⟨c + 1, Nat.succ_pos c, fun n ↦ ⟨?_, ?_⟩⟩
  · apply eq_bot_iff.mpr
    calc
      I ^ (c + 1) • ⊤ ≤ I ^ c • ⊤ :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ c))
      _ = ⊥ := (hc n).1
  · apply eq_bot_iff.mpr
    calc
      I ^ (c + 1) • ⊤ ≤ I ^ c • ⊤ :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ c))
      _ = ⊥ := (hc n).2

/-- Lemma 15.101.4 (3) (09BB): for finite `R`-modules `M` and `N`, the canonical map from the
adic completion of `Hom_R(M, N)` to the limit of the ideal-power Hom system is an isomorphism. -/
@[stacks 09BB "canonical completion comparison for the ideal-power Hom system is an isomorphism"]
theorem limitComparison_isIso
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    IsIso (limitComparison I M N) := sorry

/-- Lemma 15.101.4 (3) (09BB): the source-facing completion comparison is an isomorphism. -/
@[stacks 09BB "quotient-domain Hom-limit comparison is an isomorphism"]
theorem quotientLimitComparison_isIso
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    IsIso (quotientLimitComparison I M N) := by
  change IsIso (limitComparison I M N ≫ lim.map (quotientSystemIso I M N).inv)
  exact IsIso.comp_isIso'
    (limitComparison_isIso I M N)
    ((lim.mapIso (quotientSystemIso I M N)).isIso_inv)

/-- Lemma 15.101.4 (3) (09BB): the canonical map from the completion of `Hom_R(M, N)` to
completion-linear maps between the completed modules is an isomorphism. -/
@[stacks 09BB "canonical completed Hom comparison is an isomorphism"]
theorem completedHomComparison_isIso
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    IsIso (completedHomComparison I M N) := sorry

/-- The object-level source-facing consequence of `limitComparison_isIso`: the limit of the
ideal-power Hom system is isomorphic to the adic completion of `Hom_R(M, N)`. -/
@[stacks 09BB "limit of Hom over ideal-power quotients"]
theorem limit_isIsomorphic_adicCompletion
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    IsIsomorphic
      (limit (system I M N))
      (ModuleCat.of R (AdicCompletion I (M →ₗ[R] N))) := by
  letI := limitComparison_isIso I M N
  exact ⟨(asIso (limitComparison I M N)).symm⟩

/-- Lemma 15.101.4 (3) (09BB): the inverse limit of the source-facing quotient-domain Hom system
is isomorphic to the adic completion of `Hom_R(M, N)`. -/
@[stacks 09BB "quotient-domain Hom limit over ideal-power quotients"]
theorem quotientLimit_isIsomorphic_adicCompletion
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    IsIsomorphic
      (limit (quotientSystem I M N))
      (ModuleCat.of R (AdicCompletion I (M →ₗ[R] N))) := by
  letI := quotientLimitComparison_isIso I M N
  exact ⟨(asIso (quotientLimitComparison I M N)).symm⟩

/-- Lemma 15.101.4 (3) (09BB): the adic completion of `Hom_R(M, N)`, as a module over the
completion of `R`, is isomorphic to the module of completion-linear maps between the completed
modules. -/
@[stacks 09BB "completed Hom comparison"]
theorem completedHom_isIsomorphic_completedLinearMap
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    IsIsomorphic
      (ModuleCat.of (AdicCompletion I R) (AdicCompletion I (M →ₗ[R] N)))
      (ModuleCat.of (AdicCompletion I R)
        (AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N)) := by
  letI := completedHomComparison_isIso I M N
  exact ⟨asIso (completedHomComparison I M N)⟩

end Ideal.PowerQuotient.Hom
