/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Module.Projective.LocalRing

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal.Flat
public import ReasLib.LinearAlgebra.UniversallyInjective

/-!
# Quotient criteria for universally injective linear maps

@stack 0AS5

The statements in this file recognize tensor-stable injectivity through reductions modulo ideals
and, over a local ring, through the closed fiber.
-/

@[expose] public section

universe u v w z

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']

/-- A universally injective linear map stays injective after reduction modulo any ideal. -/
@[stacks 0AS5 "universal injectivity gives quotient injectivity"]
theorem injective_quotientMapByIdeal_of_universallyInjective (f : M →ₗ[R] M')
    (hf : UniversallyInjective.{u, v, w, max u v w z} f) (I : Ideal R) :
    Function.Injective (f.quotientMapByIdeal I) := by
  rw [quotientMapByIdeal_injective_iff_rTensor_injective]
  exact hf.rTensor_injective (R ⧸ I)

/-- If the target is flat, an `R`-linear map is universally injective exactly when its
reductions modulo all finitely generated ideals are injective. -/
@[stacks 0AS5]
theorem universallyInjective_iff_injective_mod_finite_ideal [Module.Flat R M']
    (f : M →ₗ[R] M') :
    UniversallyInjective.{u, v, w, max u v w z} f ↔
      ∀ I : Ideal R, I.FG → Function.Injective (f.quotientMapByIdeal I) := by
  constructor
  · intro hf I _
    exact injective_quotientMapByIdeal_of_universallyInjective f hf I
  · intro h
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have hx' : x ∈ (⊥ : Ideal R) • (⊤ : Submodule R M) :=
        (quotientMapByIdeal_injective_iff_mem_smul (⊥ : Ideal R) f).mp
          (h ⊥ Submodule.fg_bot) x (by simpa using hx)
      simpa using hx'
    let C := M' ⧸ f.range
    let π : M' →ₗ[R] C := Submodule.mkQ f.range
    have hπ : Function.Surjective π := Submodule.mkQ_surjective _
    have hExact : Function.Exact f π := f.exact_map_mkQ_range
    -- Local instance justification (proof-local temporary data): the cokernel flatness
    -- established here is used only to apply the exact-sequence tensor criterion below.
    letI : Module.Flat R C := Module.Flat.iff_rTensor_injective.mpr fun {I} hI ↦ by
      rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
      exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
        (f₁ := f) (f₂ := π) (g₁ := I.subtype) (g₂ := Submodule.mkQ I)
        hExact hπ (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective _)
        ((quotientMapByIdeal_injective_iff_rTensor_injective I f).mp (h I hI))
        (Module.Flat.lTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)
    intro Q _ _
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    exact LinearMap.lTensor_injective_of_exact_of_flat π hπ f hf hExact Q

end

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Flat A M]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module.Flat A N]

open IsLocalRing

/-- Over a local ring, a map from a finite flat module into a flat module is universally
injective once its reduction modulo the maximal ideal is injective. -/
@[stacks 0AS5 "local maximal-ideal companion"]
theorem universallyInjective_of_injective_mod_maximalIdeal
    (f : M →ₗ[A] N) [Module.Finite A M]
    (hf : Function.Injective (f.quotientMapByIdeal (maximalIdeal A))) :
    UniversallyInjective.{u, v, w, z} f := by
  -- Local instance justification (proof-local temporary data): finite flat modules over a
  -- local ring are free, and this proof uses a basis only within this argument.
  letI : Module.Free A M := Module.free_of_flat_of_isLocalRing
  have hfTensor : Function.Injective (f.lTensor (ResidueField A)) := by
    exact (quotientMapByIdeal_injective_iff_lTensor_injective (maximalIdeal A) f).mp hf
  let b := Module.Free.chooseBasis A M
  have hbTensor :
      LinearIndependent (ResidueField A)
        (TensorProduct.mk A (ResidueField A) M 1 ∘ b) := by
    convert (b.baseChange (ResidueField A)).linearIndependent using 1
    ext i
    simp only [Function.comp_apply, Module.Basis.baseChange_apply, TensorProduct.mk_apply]
  have hfbTensor :
      LinearIndependent (ResidueField A)
        (TensorProduct.mk A (ResidueField A) N 1 ∘ f ∘ b) := by
    rw [linearIndependent_iff'] at hbTensor ⊢
    intro s g hsum i hi
    apply hbTensor s g ?_ i hi
    apply hfTensor
    simpa only [map_sum, map_zero, Function.comp_apply, TensorProduct.mk_apply,
      ← LinearMap.smul_lTensor, LinearMap.lTensor_tmul] using hsum
  have hfb : LinearIndependent A (f ∘ b) := by
    apply Module.IsLocalRing.linearIndependent_of_flat
    simpa only [Function.comp_apply] using hfbTensor
  have hfInjective : Function.Injective f :=
    LinearMap.injective_of_linearIndependent b.span_eq hfb
  let C := N ⧸ f.range
  let π : N →ₗ[A] C := Submodule.mkQ f.range
  have hπ : Function.Surjective π := Submodule.mkQ_surjective _
  have hExact : Function.Exact f π := f.exact_map_mkQ_range
  -- Local instance justification (proof-local temporary data): the cokernel flatness
  -- established here is used only to conclude tensor-stable injectivity below.
  letI : Module.Flat A C := Module.Flat.of_forall_exists_factorization fun {l r x} hxr ↦ by
    obtain ⟨xN, hxN⟩ := Module.projective_lifting_property π x hπ
    have hxNr : π (xN r) = 0 := by
      rw [← LinearMap.comp_apply, hxN, hxr]
    have hxNr_mem : xN r ∈ f.range := by
      change Submodule.Quotient.mk (xN r) = 0 at hxNr
      rwa [Submodule.Quotient.mk_eq_zero] at hxNr
    obtain ⟨m, hm⟩ := hxNr_mem
    let d : ((Fin l →₀ A) × M) →ₗ[A] N := xN.coprod (-f)
    have hdrm : d (r, m) = 0 := by
      simp only [d, LinearMap.coprod_apply, LinearMap.neg_apply]
      rw [hm, add_neg_cancel]
    obtain ⟨q, a, y, hya, harm⟩ :=
      Module.Flat.exists_factorization_of_apply_eq_zero_of_free hdrm
    let aL : (Fin l →₀ A) →ₗ[A] (Fin q →₀ A) :=
      a.comp (LinearMap.inl A (Fin l →₀ A) M)
    let aM : M →ₗ[A] (Fin q →₀ A) :=
      a.comp (LinearMap.inr A (Fin l →₀ A) M)
    have hyL : y.comp aL = xN := by
      apply LinearMap.ext
      intro s
      simpa only [aL, d, LinearMap.comp_apply, LinearMap.inl_apply,
        LinearMap.coprod_apply, map_zero, add_zero] using
        (LinearMap.congr_fun hya (s, 0)).symm
    have hyM : y.comp aM = -f := by
      apply LinearMap.ext
      intro n
      simpa only [aM, d, LinearMap.comp_apply, LinearMap.inr_apply,
        LinearMap.coprod_apply, map_zero, zero_add] using
        (LinearMap.congr_fun hya (0, n)).symm
    have haMTensor : Function.Injective (aM.lTensor (ResidueField A)) := by
      intro s t hst
      apply hfTensor
      have := congrArg (y.lTensor (ResidueField A)) hst
      simpa only [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hyM,
        LinearMap.lTensor_neg, LinearMap.neg_apply, neg_inj] using this
    obtain ⟨sM, hsM⟩ :=
      (IsLocalRing.split_injective_iff_lTensor_residueField_injective aM).mpr haMTensor
    let p : (Fin q →₀ A) →ₗ[A] (Fin q →₀ A) := LinearMap.id - aM.comp sM
    have hpM (n : M) : p (aM n) = 0 := by
      simp only [p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
      have hsMn : sM (aM n) = n := by
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
          LinearMap.congr_fun hsM n
      rw [hsMn, sub_self]
    have ha_decomp : aL r + aM m = 0 := by
      simp only [aL, aM, LinearMap.comp_apply, LinearMap.inl_apply,
        LinearMap.inr_apply]
      rw [← map_add]
      simpa using harm
    have hpr : p (aL r) = 0 := by
      have := congrArg p ha_decomp
      simpa only [map_add, hpM, add_zero, map_zero] using this
    refine ⟨q, p.comp aL, π.comp y, ?_, ?_⟩
    · apply LinearMap.ext
      intro s
      simp only [LinearMap.comp_apply]
      symm
      have hyLs : y (aL s) = xN s := by
        simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hyL s
      have hyMs : y (aM (sM (aL s))) = -f (sM (aL s)) := by
        simpa only [LinearMap.comp_apply, LinearMap.neg_apply] using
          LinearMap.congr_fun hyM (sM (aL s))
      calc
        π (y (p (aL s))) =
            π (y (aL s - aM (sM (aL s)))) := by rfl
        _ = π (y (aL s)) - π (y (aM (sM (aL s)))) := by simp
        _ = π (xN s) - π (-f (sM (aL s))) := by
          rw [hyLs, hyMs]
        _ = x s := by
          rw [← LinearMap.comp_apply, hxN]
          have : π (f (sM (aL s))) = 0 := by
            rw [← LinearMap.comp_apply, hExact.linearMap_comp_eq_zero,
              LinearMap.zero_apply]
          simp [this]
    · exact hpr
  intro Q _ _
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  exact LinearMap.lTensor_injective_of_exact_of_flat π hπ f hfInjective hExact Q

end

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Projective R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Flat R N]

open IsLocalRing

/-- Over a commutative local ring, a linear map from a projective module to a flat module is
universally injective if its reduction modulo the maximal ideal is injective. -/
@[stacks 05FQ]
theorem universallyInjective_of_projective_of_injective_mod_maximalIdeal
    (f : M →ₗ[R] N)
    (hbar : Function.Injective (f.quotientMapByIdeal (maximalIdeal R))) :
    UniversallyInjective.{u, v, w, z} f := sorry

end

end LinearMap
