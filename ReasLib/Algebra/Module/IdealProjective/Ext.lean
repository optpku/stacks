/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Module.ProjectiveFactorIdeal
public import ReasLib.CategoryTheory.Linear.IdealProjective.Ext

@[expose] public section

/-!
# Extension criteria for ideal-projective modules

This file identifies the module-theoretic projective-factor ideal with the category-level
factorisation property and exposes the `Ext¹` criterion both atomically and as the source-facing
three-condition `List.TFAE`.

@stack 0G92
-/

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

universe u v

/-- Translate a structured module factorisation to the corresponding categorical one. -/
private theorem module_factor_iff_category {R : Type u} [CommRing R]
    {M N : ModuleCat.{max u v} R} (f : M →ₗ[R] N) :
    f.FactorsThroughProjective ↔
      (isProjective (ModuleCat.{max u v} R)).factorThru (ModuleCat.ofHom f) := by
  constructor
  · rintro ⟨F⟩
    letI : AddCommGroup F.mid := Module.addCommMonoidToAddCommGroup R
    letI : Module.Projective R F.mid := F.projective
    exact ⟨{
      base :=
        { mid := ModuleCat.of R F.mid
          ι := ModuleCat.ofHom F.fromSource
          π := ModuleCat.ofHom F.toTarget
          ι_π := ModuleCat.hom_ext F.base.factor }
      mem := inferInstance }⟩
  · rintro ⟨F⟩
    letI : Projective F.base.mid := F.mem
    exact ⟨LinearMap.Factorisation.Projective.ofMaps F.base.mid F.base.ι.hom F.base.π.hom
      (ModuleCat.hom_ext_iff.mp F.base.ι_π)⟩

/-- Detect a projective factorisation using the extension of a projective presentation. -/
private theorem category_factor_iff_ext_one {R : Type u} [CommRing R]
    {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    (isProjective (ModuleCat.{max u v} R)).factorThru f ↔
      ∀ (Z : ModuleCat.{max u v} R) (e : Ext N Z 1),
        (mk₀ f).comp e (zero_add 1) = 0 := by
  constructor
  · rintro ⟨F⟩ Z e
    letI : Projective F.base.mid := F.mem
    rw [← F.base.ι_π, ← mk₀_comp_mk₀_assoc,
      ((mk₀ F.base.π).comp e (zero_add 1)).eq_zero_of_projective, comp_zero]
  · intro h
    obtain ⟨P⟩ := EnoughProjectives.presentation N
    let S := ShortComplex.mk _ _ (Limits.kernel.condition P.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel P.f }
    obtain ⟨e, he⟩ := covariant_sequence_exact₃ M hS (mk₀ f) (zero_add 1) (h _ _)
    obtain ⟨g, rfl⟩ := homEquiv₀.symm.surjective e
    have hg : g ≫ P.f = f := homEquiv₀.symm.injective (by simpa using he)
    exact ⟨{ base := { mid := P.p, ι := g, π := P.f, ι_π := hg }
             mem := inferInstance }⟩

namespace Module.projectiveFactorIdeal

variable {R : Type u} [CommRing R]
variable {M : ModuleCat.{max u v} R}

/-- The projective-factor ideal is the intersection of the annihilators of all degree-one
extension groups out of the module. -/
@[stacks 0G92 "projective-factor ideal detected by Ext-one"]
theorem eq_iInf_annihilator_ext_one :
    Module.projectiveFactorIdeal R M =
      ⨅ N : ModuleCat.{max u v} R, Module.annihilator R (Ext M N 1) := by
  ext a
  change (LinearMap.lsmul R M a).FactorsThroughProjective ↔ _
  rw [module_factor_iff_category, category_factor_iff_ext_one]
  simp only [ModuleCat.lsmul_eq_smul_id, mk₀_smul, smul_comp, mk₀_id_comp,
    Ideal.mem_iInf, Module.mem_annihilator]

end Module.projectiveFactorIdeal

namespace Module.IsIdealProjective

variable {R : Type u} [CommRing R]
variable {I : Ideal R} {M : ModuleCat.{max u v} R}

/-- Module ideal-projectivity agrees with ideal-projectivity of the associated object of
`ModuleCat R`. -/
theorem iff_category :
    Module.IsIdealProjective I M ↔ CategoryTheory.idealProjective I M := by
  constructor
  · intro h a
    exact (module_factor_iff_category (LinearMap.lsmul R M (a : R))).mp (h a.2)
  · intro h a ha
    exact (module_factor_iff_category (LinearMap.lsmul R M a)).mpr (h ⟨a, ha⟩)

/-- Ideal-projectivity is equivalently pointwise factorisation of the scalar endomorphisms
through free modules. -/
theorem iff_factorsThroughFree :
    Module.IsIdealProjective I M ↔
      ∀ a : I, (LinearMap.lsmul R M (a : R)).FactorsThroughFree := by
  constructor
  · intro h a
    obtain ⟨F⟩ : (LinearMap.lsmul R M (a : R)).FactorsThroughProjective := h a.2
    obtain ⟨s, hs⟩ := F.projective.out
    let π : (F.mid →₀ R) →ₗ[R] F.mid := Finsupp.linearCombination R (fun x ↦ x)
    refine ⟨LinearMap.Factorisation.Free.ofMaps (F.mid →₀ R)
      (s.comp F.fromSource) (F.toTarget.comp π) ?_⟩
    ext x
    change F.toTarget ((Finsupp.linearCombination R id) (s (F.fromSource x))) = _
    rw [hs]
    exact DFunLike.congr_fun F.base.factor x
  · intro h a ha
    obtain ⟨F⟩ := h ⟨a, ha⟩
    exact ⟨F.toProjective⟩

/-- An ideal-projective module has every positive-degree extension group annihilated by the
ideal. -/
theorem le_annihilator_ext (h : Module.IsIdealProjective I M)
    (N : ModuleCat.{max u v} R)
    {n : ℕ} (hn : 0 < n) : I ≤ Module.annihilator R (Ext M N n) := by
  cases n with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ n =>
    intro a ha
    apply Module.mem_annihilator.mpr
    intro e
    obtain ⟨F⟩ := iff_category.mp h ⟨a, ha⟩
    letI : CategoryTheory.Projective F.base.mid := F.mem
    calc
      a • e = (mk₀ (a • 𝟙 M)).comp e (zero_add _) := by
        rw [mk₀_smul, smul_comp, mk₀_id_comp]
      _ = (mk₀ F.base.ι).comp ((mk₀ F.base.π).comp e (zero_add _)) (zero_add _) := by
        rw [mk₀_comp_mk₀_assoc, F.base.ι_π]
      _ = 0 := by
        rw [((mk₀ F.base.π).comp e (zero_add _)).eq_zero_of_projective, comp_zero]

/-- Ideal-projectivity is equivalent to annihilation of all degree-one extension groups. -/
@[stacks 0G92 "Ext-one criterion for ideal-projective modules"]
theorem iff_ext_one_annihilator :
    Module.IsIdealProjective I M ↔
      ∀ N : ModuleCat.{max u v} R, I ≤ Module.annihilator R (Ext M N 1) := by
  change I ≤ Module.projectiveFactorIdeal R M ↔ _
  rw [Module.projectiveFactorIdeal.eq_iInf_annihilator_ext_one, le_iInf_iff]

/-- Pointwise version of the `Ext¹` annihilator criterion. -/
theorem iff_ext_one_smul_eq_zero :
    Module.IsIdealProjective I M ↔
      ∀ (N : ModuleCat.{max u v} R) (a : I) (e : Ext M N 1), (a : R) • e = 0 := by
  rw [iff_ext_one_annihilator]
  constructor
  · intro h N a e
    exact Module.mem_annihilator.mp (h N a.2) e
  · intro h N a ha
    exact Module.mem_annihilator.mpr (h N ⟨a, ha⟩)

/-- Lemma 15.71.3: projective factorisation, free factorisation, and annihilation of every
degree-one extension group are equivalent. -/
@[stacks 0G92 "projective, free, and Ext-one characterizations"]
theorem tfae :
    List.TFAE
      [ Module.IsIdealProjective I M
      , ∀ a : I, (LinearMap.lsmul R M (a : R)).FactorsThroughFree
      , ∀ N : ModuleCat.{max u v} R, I ≤ Module.annihilator R (Ext M N 1) ] := by
  rw [← iff_factorsThroughFree.{u, v} (I := I) (M := M),
    ← iff_ext_one_annihilator.{u, v} (I := I) (M := M)]
  simp only [List.tfae_cons_self, List.tfae_singleton]

end Module.IsIdealProjective
