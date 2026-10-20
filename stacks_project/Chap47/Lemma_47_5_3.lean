/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Injective.Hull
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 47.5.3 (1): A linear map between modules extends to a linear map between
their injective hulls, compatibly with the hull embeddings. -/
@[stacks 08Y4] #check (LinearMap.IsInjectiveHull.exists_lift :
  ∀ {R : Type u} [Ring R]
    {M N E E' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E] [AddCommGroup E']
    [Module R M] [Module R N] [Module R E] [Module R E']
    [Module.Injective R E] [Module.Injective R E']
    {i : M →ₗ[R] E} {j : N →ₗ[R] E'},
    i.IsInjectiveHull → j.IsInjectiveHull → ∀ φ : M →ₗ[R] N,
      ∃ ψ : E →ₗ[R] E', ψ.comp i = j.comp φ)

/- Lemma 47.5.3 (2): An injective linear map between modules extends injectively
between their injective hulls. -/
@[stacks 08Y4] #check (LinearMap.IsInjectiveHull.exists_injective_lift :
  ∀ {R : Type u} [Ring R]
    {M N E E' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E] [AddCommGroup E']
    [Module R M] [Module R N] [Module R E] [Module R E']
    [Module.Injective R E] [Module.Injective R E']
    {i : M →ₗ[R] E} {j : N →ₗ[R] E'},
    i.IsInjectiveHull → j.IsInjectiveHull → ∀ {φ : M →ₗ[R] N},
      Function.Injective φ →
        ∃ ψ : E →ₗ[R] E', ψ.comp i = j.comp φ ∧ Function.Injective ψ)

/- Lemma 47.5.3 (3): An essential injection between modules extends to a linear
equivalence between their injective hulls. -/
@[stacks 08Y4] #check (LinearMap.IsInjectiveHull.exists_linearEquiv_of_essential :
  ∀ {R : Type u} [Ring R]
    {M N E E' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E] [AddCommGroup E']
    [Module R M] [Module R N] [Module R E] [Module R E']
    [Module.Injective R E] [Module.Injective R E']
    {i : M →ₗ[R] E} {j : N →ₗ[R] E'},
    i.IsInjectiveHull → j.IsInjectiveHull → ∀ {φ : M →ₗ[R] N},
      Function.Injective φ →
        (∀ P : Submodule R N, P ≠ ⊥ → φ.range ⊓ P ≠ ⊥) →
          ∃ e : E ≃ₗ[R] E', e.toLinearMap.comp i = j.comp φ)

/- Lemma 47.5.3 (4): A bijective linear map between modules extends to a compatible
linear equivalence between their injective hulls. -/
@[stacks 08Y4] #check (LinearMap.IsInjectiveHull.exists_linearEquiv_of_bijective :
  ∀ {R : Type u} [Ring R]
    {M N E E' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E] [AddCommGroup E']
    [Module R M] [Module R N] [Module R E] [Module R E']
    [Module.Injective R E] [Module.Injective R E']
    {i : M →ₗ[R] E} {j : N →ₗ[R] E'},
    i.IsInjectiveHull → j.IsInjectiveHull → ∀ {φ : M →ₗ[R] N},
      Function.Bijective φ →
        ∃ e : E ≃ₗ[R] E', e.toLinearMap.comp i = j.comp φ)

/- Lemma 47.5.3 (5): An embedding of a module into an injective module identifies
that module with the product of its injective hull and a complementary module. -/
@[stacks 08Y4] #check (LinearMap.IsInjectiveHull.exists_complement :
  ∀ {R : Type u} [Ring R]
    {M E I : Type v}
    [AddCommGroup M] [AddCommGroup E] [AddCommGroup I]
    [Module R M] [Module R E] [Module R I]
    [Module.Injective R E] [Module.Injective R I]
    {i : M →ₗ[R] E},
    i.IsInjectiveHull → ∀ {k : M →ₗ[R] I}, Function.Injective k →
      ∃ (I' : Type v) (_ : AddCommGroup I') (_ : Module R I') (e : I ≃ₗ[R] E × I'),
        e.toLinearMap.comp k = (LinearMap.inl R E I').comp i)

/- Lemma 47.5.3 (6): Any two injective hulls of a module are linearly equivalent
by an equivalence compatible with their hull embeddings. -/
@[stacks 08Y4] #check (LinearMap.IsInjectiveHull.exists_linearEquiv :
  ∀ {R : Type u} [Ring R]
    {M E E' : Type v}
    [AddCommGroup M] [AddCommGroup E] [AddCommGroup E']
    [Module R M] [Module R E] [Module R E']
    [Module.Injective R E] [Module.Injective R E']
    {i : M →ₗ[R] E} {j : M →ₗ[R] E'},
    i.IsInjectiveHull → j.IsInjectiveHull →
      ∃ e : E ≃ₗ[R] E', e.toLinearMap.comp i = j)
