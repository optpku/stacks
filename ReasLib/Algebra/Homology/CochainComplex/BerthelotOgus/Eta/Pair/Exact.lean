/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Pair

/-!
# The exact row associated to the visible-power eta pair

The pair map `(1, d)` is the kernel of the complementary map `(d, -1)`.  Restricting the latter
to its range gives a canonical short exact row whose splitting is controlled by projectivity of
that range.
@stack 0F7W
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CochainComplex.BerthelotOgus.Nat.Pair

variable {A : Type u} [CommRing A]

private theorem mem_principalIdeal_smul_top_iff
    {M : Type v} [AddCommGroup M] [Module A M] (a : A) (x : M) :
    x ∈ principalIdeal a • (⊤ : Submodule A M) ↔
      x ∈ LinearMap.range (LinearMap.lsmul A M a) := by
  rw [principalIdeal, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]
  rfl

/-- The target `f^n K^(n+1)` of the complementary map `(d, -1)`. -/
def deltaTarget (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    Submodule A (K.X (n + 1)) :=
  principalIdeal (f ^ n) • (⊤ : Submodule A (K.X (n + 1)))

/-- The differential sends the first visible power submodule into `deltaTarget`. -/
theorem differential_mem_deltaTarget
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (x : powerSubmodule f K n) : (K.d n (n + 1)).hom x ∈ deltaTarget f K n := by
  exact Submodule.smul_top_le_comap_smul_top (principalIdeal (f ^ n))
    (K.d n (n + 1)).hom x.property

/-- The next visible power submodule is contained in `deltaTarget`. -/
theorem nextPowerSubmodule_le_deltaTarget
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    nextPowerSubmodule f K n ≤ deltaTarget f K n := by
  exact Submodule.smul_mono_left
    (Ideal.span_singleton_le_span_singleton.mpr ⟨f, pow_succ f n⟩)

/-- The differential on the first visible power, with codomain restricted to `deltaTarget`. -/
def differentialToDelta
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    powerSubmodule f K n →ₗ[A] deltaTarget f K n :=
  ((K.d n (n + 1)).hom.comp (powerSubmodule f K n).subtype).codRestrict
    (deltaTarget f K n) (differential_mem_deltaTarget f K n)

private theorem differentialToDelta_val
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (x : powerSubmodule f K n) :
    (differentialToDelta f K n x).1 = (K.d n (n + 1)).hom x.1 := rfl

/-- The complementary map `(d, -1)` on the two visible power submodules. -/
@[stacks 0F7W "complementary map for the Berthelot-Ogus eta pair"]
def deltaLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    powerSubmodule f K n × nextPowerSubmodule f K n →ₗ[A] deltaTarget f K n :=
  ((differentialToDelta f K n).comp
      (LinearMap.fst A (powerSubmodule f K n) (nextPowerSubmodule f K n))) -
    ((Submodule.inclusion (nextPowerSubmodule_le_deltaTarget f K n)).comp
      (LinearMap.snd A (powerSubmodule f K n) (nextPowerSubmodule f K n)))

private theorem pairLinear_snd_val
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) (x : term f K n) :
    (pairLinear f K n x).2.1 = (K.d n (n + 1)).hom x.1 := by
  change ((eta f K).d n (n + 1) x).1 = (K.d n (n + 1)).hom x.1
  rw [eta_d]
  rfl

private theorem deltaLinear_val
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (x : powerSubmodule f K n × nextPowerSubmodule f K n) :
    (deltaLinear f K n x).1 = (K.d n (n + 1)).hom x.1.1 - x.2.1 := by
  calc
    (deltaLinear f K n x).1 =
        (differentialToDelta f K n x.1 -
          Submodule.inclusion (nextPowerSubmodule_le_deltaTarget f K n) x.2).1 :=
      congrArg Subtype.val (LinearMap.sub_apply
        ((differentialToDelta f K n).comp
          (LinearMap.fst A (powerSubmodule f K n) (nextPowerSubmodule f K n)))
        ((Submodule.inclusion (nextPowerSubmodule_le_deltaTarget f K n)).comp
          (LinearMap.snd A (powerSubmodule f K n) (nextPowerSubmodule f K n))) x)
    _ = (differentialToDelta f K n x.1).1 -
        (Submodule.inclusion (nextPowerSubmodule_le_deltaTarget f K n) x.2).1 :=
      Submodule.coe_sub _ _ _
    _ = _ := congrArg₂ (fun a b : K.X (n + 1) ↦ a - b)
      (differentialToDelta_val f K n x.1)
      (Submodule.coe_inclusion (nextPowerSubmodule_le_deltaTarget f K n) x.2)

private theorem deltaLinear_eq_zero_iff
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (x : powerSubmodule f K n × nextPowerSubmodule f K n) :
    deltaLinear f K n x = 0 ↔ (K.d n (n + 1)).hom x.1.1 = x.2.1 := by
  rw [Subtype.ext_iff, deltaLinear_val, Submodule.coe_zero, sub_eq_zero]

/-- The complementary map vanishes after the visible-power pair map. -/
theorem deltaLinear_comp_pairLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (deltaLinear f K n).comp (pairLinear f K n) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (K.d n (n + 1)).hom x.1 - ((eta f K).d n (n + 1) x).1 = 0
  rw [eta_d]
  exact sub_self _

/-- The kernel of `(d, -1)` is the range of the visible-power pair map `(1, d)`. -/
theorem ker_deltaLinear_eq_range_pairLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    LinearMap.ker (deltaLinear f K n) = LinearMap.range (pairLinear f K n) := by
  apply Submodule.ext
  intro x
  rw [LinearMap.mem_ker, deltaLinear_eq_zero_iff, LinearMap.mem_range]
  constructor
  · intro hdx
    have hxterm : x.1.1 ∈ term f K n := by
      constructor
      · exact (mem_principalIdeal_smul_top_iff (f ^ n) x.1.1).mp x.1.2
      · change (K.d n (n + 1)).hom x.1.1 ∈
          LinearMap.range (LinearMap.lsmul A (K.X (n + 1)) (f ^ (n + 1)))
        rw [hdx]
        exact (mem_principalIdeal_smul_top_iff (f ^ (n + 1)) x.2.1).mp x.2.2
    refine ⟨⟨x.1.1, hxterm⟩, ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rw [pairLinear_snd_val]
      exact hdx
  · rintro ⟨y, rfl⟩
    rw [pairLinear_snd_val]
    rfl

/-- The range-restricted complementary map vanishes after the visible-power pair map. -/
theorem deltaLinear_rangeRestrict_comp_pairLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (deltaLinear f K n).rangeRestrict.comp (pairLinear f K n) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (deltaLinear_comp_pairLinear f K n) x

/-- The canonical exact row from an eta term through the two visible power submodules to the
range of `(d, -1)`. -/
@[stacks 0F7W "exact row for a Berthelot-Ogus eta term"]
def rangeShortComplex
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    ShortComplex (ModuleCat.{v} A) :=
  ShortComplex.mk
    (ModuleCat.ofHom (pairLinear f K n))
    (ModuleCat.ofHom (deltaLinear f K n).rangeRestrict)
    (congrArg ModuleCat.ofHom (deltaLinear_rangeRestrict_comp_pairLinear f K n))

/-- The canonical eta pair row is short exact. -/
theorem rangeShortComplex_shortExact
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (rangeShortComplex f K n).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
    change LinearMap.range (pairLinear f K n) =
      LinearMap.ker (deltaLinear f K n).rangeRestrict
    rw [LinearMap.ker_rangeRestrict, ker_deltaLinear_eq_range_pairLinear]
  · apply (ModuleCat.mono_iff_injective _).2
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : powerSubmodule f K n × nextPowerSubmodule f K n ↦ z.1.1) h
  · change Epi (ModuleCat.ofHom (deltaLinear f K n).rangeRestrict)
    exact (ModuleCat.epi_iff_surjective _).2 (LinearMap.surjective_rangeRestrict _)

/-- Projectivity of the complementary range splits the visible-power pair inclusion. -/
theorem pairLinear_isSplitMono_of_deltaRange_projective
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Projective A (LinearMap.range (deltaLinear f K n))] :
    IsSplitMono (ModuleCat.ofHom (pairLinear f K n)) := by
  haveI : CategoryTheory.Projective (rangeShortComplex f K n).X₃ := by
    change CategoryTheory.Projective (ModuleCat.of A (LinearMap.range (deltaLinear f K n)))
    infer_instance
  exact (rangeShortComplex_shortExact f K n).splittingOfProjective.isSplitMono_f

end CochainComplex.BerthelotOgus.Nat.Pair
