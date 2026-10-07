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

namespace Module.projectiveFactorIdeal

variable {R : Type u} [CommRing R]
variable {M : ModuleCat.{max u v} R}

/-- The projective-factor ideal is the intersection of the annihilators of all degree-one
extension groups out of the module. -/
@[stacks 0G92 "projective-factor ideal detected by Ext-one"]
theorem eq_iInf_annihilator_ext_one :
    Module.projectiveFactorIdeal R M =
      ⨅ N : ModuleCat.{max u v} R, Module.annihilator R (Ext M N 1) := sorry

end Module.projectiveFactorIdeal

namespace Module.IsIdealProjective

variable {R : Type u} [CommRing R]
variable {I : Ideal R} {M : ModuleCat.{max u v} R}

/-- Module ideal-projectivity agrees with ideal-projectivity of the associated object of
`ModuleCat R`. -/
theorem iff_category :
    Module.IsIdealProjective I M ↔ CategoryTheory.idealProjective I M := sorry

/-- Ideal-projectivity is equivalently pointwise factorisation of the scalar endomorphisms
through free modules. -/
theorem iff_factorsThroughFree :
    Module.IsIdealProjective I M ↔
      ∀ a : I, (LinearMap.lsmul R M (a : R)).FactorsThroughFree := sorry

/-- An ideal-projective module has every positive-degree extension group annihilated by the
ideal. -/
theorem le_annihilator_ext (h : Module.IsIdealProjective I M)
    (N : ModuleCat.{max u v} R)
    {n : ℕ} (hn : 0 < n) : I ≤ Module.annihilator R (Ext M N n) := sorry

/-- Ideal-projectivity is equivalent to annihilation of all degree-one extension groups. -/
@[stacks 0G92 "Ext-one criterion for ideal-projective modules"]
theorem iff_ext_one_annihilator :
    Module.IsIdealProjective I M ↔
      ∀ N : ModuleCat.{max u v} R, I ≤ Module.annihilator R (Ext M N 1) := sorry

/-- Pointwise version of the `Ext¹` annihilator criterion. -/
theorem iff_ext_one_smul_eq_zero :
    Module.IsIdealProjective I M ↔
      ∀ (N : ModuleCat.{max u v} R) (a : I) (e : Ext M N 1), (a : R) • e = 0 := sorry

/-- Lemma 15.71.3: projective factorisation, free factorisation, and annihilation of every
degree-one extension group are equivalent. -/
@[stacks 0G92 "projective, free, and Ext-one characterizations"]
theorem tfae :
    List.TFAE
      [ Module.IsIdealProjective I M
      , ∀ a : I, (LinearMap.lsmul R M (a : R)).FactorsThroughFree
      , ∀ N : ModuleCat.{max u v} R, I ≤ Module.annihilator R (Ext M N 1) ] := sorry

end Module.IsIdealProjective
