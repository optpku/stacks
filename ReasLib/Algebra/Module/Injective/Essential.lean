/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Injective

@[expose] public section

universe u v

/-- A submodule of an injective module is injective exactly when it has no proper
essential extension inside the ambient module. -/
theorem Submodule.injective_iff_eq_of_essential_extension
    {R : Type u} [Ring R] {I : Type v} [AddCommGroup I] [Module R I]
    [Module.Injective R I] (E : Submodule R I) :
    Module.Injective R E ↔
      ∀ E' : Submodule R I, E ≤ E' →
        (∀ P : Submodule R I, P ≤ E' → P ≠ ⊥ → E ⊓ P ≠ ⊥) → E = E' := sorry

/-- A module is injective exactly when every injective linear map from it with
essential range is surjective. -/
theorem Module.injective_iff_surjective_of_essential_extension
    {R : Type u} [Ring R] (E : Type v) [AddCommGroup E] [Module R E] :
    Module.Injective R E ↔
      ∀ {M : Type v} [AddCommGroup M] [Module R M] (f : E →ₗ[R] M),
        Function.Injective f →
          (∀ P : Submodule R M, P ≠ ⊥ → LinearMap.range f ⊓ P ≠ ⊥) →
            Function.Surjective f := sorry
