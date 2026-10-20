module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import ReasLib.CategoryTheory.Abelian.Projective.Schanuel
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Schanuel's lemma for modules

This file contains only the concrete `LinearMap` views of the categorical owner API.

@stack 00O3
-/

noncomputable section

universe u v

namespace Module.Schanuel

variable {R : Type u} [Ring R]

/-- The low-parameter module form of Schanuel's lemma: the kernels of two surjections from
projective modules become equivalent after adjoining the other projective module. -/
@[stacks 00O3 "kernel-product Schanuel equivalence"]
noncomputable def kernelProdEquiv
    {M P₁ P₂ : Type v}
    [AddCommGroup M] [Module R M]
    [AddCommGroup P₁] [Module R P₁] [Module.Projective R P₁]
    [AddCommGroup P₂] [Module R P₂] [Module.Projective R P₂]
    (p₁ : P₁ →ₗ[R] M) (p₂ : P₂ →ₗ[R] M)
    (hp₁ : Function.Surjective p₁) (hp₂ : Function.Surjective p₂) :
    (LinearMap.ker p₁ × P₂) ≃ₗ[R] (LinearMap.ker p₂ × P₁) :=
  (((ModuleCat.biprodIsoProd (ModuleCat.of.{v} R (LinearMap.ker p₁))
      (ModuleCat.of.{v} R P₂)).symm ≪≫
    CategoryTheory.ShortComplex.ShortExact.schanuelIso
      (LinearMap.shortExact_shortComplexKer hp₁)
      (LinearMap.shortExact_shortComplexKer hp₂)
      (CategoryTheory.Iso.refl (ModuleCat.of.{v} R M)) ≪≫
    ModuleCat.biprodIsoProd (ModuleCat.of.{v} R P₁)
      (ModuleCat.of.{v} R (LinearMap.ker p₂))).toLinearEquiv).trans
    (LinearEquiv.prodComm R P₁ (LinearMap.ker p₂))

/-- Linear-map presentation view of Schanuel's lemma.  Exactness identifies the supplied source
modules with the kernels used by `kernelProdEquiv`. -/
@[stacks 00O3 "linear-map Schanuel equivalence"]
noncomputable def ofExact
    {K L M P₁ P₂ : Type v}
    [AddCommGroup K] [Module R K]
    [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    [AddCommGroup P₁] [Module R P₁] [Module.Projective R P₁]
    [AddCommGroup P₂] [Module R P₂] [Module.Projective R P₂]
    (c₁ : K →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] M)
    (c₂ : L →ₗ[R] P₂) (p₂ : P₂ →ₗ[R] M)
    (hc₁ : Function.Injective c₁) (h₁ : Function.Exact c₁ p₁)
    (hp₁ : Function.Surjective p₁) (hc₂ : Function.Injective c₂)
    (h₂ : Function.Exact c₂ p₂) (hp₂ : Function.Surjective p₂) :
    (K × P₂) ≃ₗ[R] (L × P₁) :=
  let eK := (LinearEquiv.ofInjective c₁ hc₁).trans
    (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp h₁).symm)
  let eL := (LinearEquiv.ofInjective c₂ hc₂).trans
    (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp h₂).symm)
  (eK.prodCongr (LinearEquiv.refl R P₂)).trans
    (LinearEquiv.trans (kernelProdEquiv p₁ p₂ hp₁ hp₂)
      (eL.symm.prodCongr (LinearEquiv.refl R P₁)))

section Computation

variable {K L M P₁ P₂ : Type v}
variable [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup P₁] [Module R P₁] [Module.Projective R P₁]
variable [AddCommGroup P₂] [Module R P₂] [Module.Projective R P₂]
variable (c₁ : K →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] M)
variable (c₂ : L →ₗ[R] P₂) (p₂ : P₂ →ₗ[R] M)
variable (hc₁ : Function.Injective c₁) (h₁ : Function.Exact c₁ p₁)
variable (hp₁ : Function.Surjective p₁) (hc₂ : Function.Injective c₂)
variable (h₂ : Function.Exact c₂ p₂) (hp₂ : Function.Surjective p₂)

/-- The second component of the exact-presentation comparison is the kernel-product comparison
applied to the supplied inclusion of the first kernel. -/
theorem ofExact_apply_snd (k : K) (y : P₂) :
    (ofExact c₁ p₁ c₂ p₂ hc₁ h₁ hp₁ hc₂ h₂ hp₂ (k, y)).2 =
      (kernelProdEquiv p₁ p₂ hp₁ hp₂
        (⟨c₁ k, h₁.apply_apply_eq_zero k⟩, y)).2 := sorry

/-- The supplied inclusion of the second kernel identifies the first component of the
exact-presentation comparison with the first component of the kernel-product comparison. -/
theorem ofExact_apply_fst (k : K) (y : P₂) :
    c₂ (ofExact c₁ p₁ c₂ p₂ hc₁ h₁ hp₁ hc₂ h₂ hp₂ (k, y)).1 =
      ((kernelProdEquiv p₁ p₂ hp₁ hp₂
        (⟨c₁ k, h₁.apply_apply_eq_zero k⟩, y)).1 : P₂) := sorry

end Computation

/-- Existence-only form of the linear-map Schanuel equivalence. -/
@[stacks 00O3 "existence of a linear-map Schanuel equivalence"]
theorem nonempty_ofExact
    {K L M P₁ P₂ : Type v}
    [AddCommGroup K] [Module R K]
    [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    [AddCommGroup P₁] [Module R P₁] [Module.Projective R P₁]
    [AddCommGroup P₂] [Module R P₂] [Module.Projective R P₂]
    (c₁ : K →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] M)
    (c₂ : L →ₗ[R] P₂) (p₂ : P₂ →ₗ[R] M)
    (hc₁ : Function.Injective c₁) (h₁ : Function.Exact c₁ p₁)
    (hp₁ : Function.Surjective p₁) (hc₂ : Function.Injective c₂)
    (h₂ : Function.Exact c₂ p₂) (hp₂ : Function.Surjective p₂) :
    Nonempty ((K × P₂) ≃ₗ[R] (L × P₁)) :=
  ⟨ofExact c₁ p₁ c₂ p₂ hc₁ h₁ hp₁ hc₂ h₂ hp₂⟩

end Module.Schanuel
