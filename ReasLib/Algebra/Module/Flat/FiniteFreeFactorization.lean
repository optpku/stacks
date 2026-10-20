/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-free factorization criterion for flat modules

@stack 058E
-/

@[expose] public section

universe u v w

namespace Module.Flat

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.81.2: `M` is flat exactly when every map from a finitely
presented module to `M` factors through a finite-free module. -/
@[stacks 058E]
theorem iff_finiteFree_factorization :
    Module.Flat R M ↔
      ∀ {P : Type w} [AddCommGroup P] [Module R P]
        [Module.FinitePresentation R P] (f : P →ₗ[R] M),
        ∃ (n : ℕ) (h : P →ₗ[R] (Fin n →₀ R))
          (g : (Fin n →₀ R) →ₗ[R] M), f = g.comp h := sorry

end Module.Flat
