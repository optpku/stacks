/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Filtration
import Mathlib.Tactic.CrossRefAttribute

/-!
# Artin-Rees Cutoffs for Ideals

The standard Artin-Rees cutoff can be increased without changing the eventual formula.  This
file packages that monotonicity together with lower-bounded and positive cutoff constructors.

@stack 00IN
-/

@[expose] public section

open scoped Pointwise

universe u v

variable {R : Type u} {M : Type v}
variable [CommRing R] [AddCommGroup M] [Module R M]

namespace Ideal

/-- Increasing an Artin-Rees cutoff preserves the eventual Artin-Rees formula. -/
@[stacks 00IN "increasing an Artin-Rees cutoff"]
theorem pow_inf_eq_pow_smul_of_le
    (I : Ideal R) (N : Submodule R M) {k c : ℕ}
    (hk : ∀ n ≥ k,
      I ^ n • ⊤ ⊓ N = I ^ (n - k) • (I ^ k • ⊤ ⊓ N))
    (hkc : k ≤ c) :
    ∀ n ≥ c,
      I ^ n • ⊤ ⊓ N = I ^ (n - c) • (I ^ c • ⊤ ⊓ N) := by
  intro n hcn
  calc
    I ^ n • ⊤ ⊓ N = I ^ (n - k) • (I ^ k • ⊤ ⊓ N) := hk n (hkc.trans hcn)
    _ = I ^ ((n - c) + (c - k)) • (I ^ k • ⊤ ⊓ N) := by
      congr 2
      omega
    _ = I ^ (n - c) • (I ^ (c - k) • (I ^ k • ⊤ ⊓ N)) := by
      rw [pow_add, smul_smul]
    _ = I ^ (n - c) • (I ^ c • ⊤ ⊓ N) := by
      rw [← hk c hkc]

/-- An Artin-Rees cutoff can be chosen above any prescribed lower bound. -/
@[stacks 00IN "Artin-Rees cutoff above a prescribed bound"]
theorem exists_ge_pow_inf_eq_pow_smul
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (N : Submodule R M) (c₀ : ℕ) :
    ∃ c ≥ c₀, ∀ n ≥ c,
      I ^ n • ⊤ ⊓ N = I ^ (n - c) • (I ^ c • ⊤ ⊓ N) := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul N
  refine ⟨max k c₀, le_max_right _ _, ?_⟩
  exact pow_inf_eq_pow_smul_of_le I N hk (le_max_left _ _)

/-- A positive Artin-Rees cutoff exists for finite modules over Noetherian rings. -/
@[stacks 00IN "positive Artin-Rees cutoff"]
theorem exists_pos_pow_inf_eq_pow_smul
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (N : Submodule R M) :
    ∃ c > 0, ∀ n ≥ c,
      I ^ n • ⊤ ⊓ N = I ^ (n - c) • (I ^ c • ⊤ ⊓ N) := by
  obtain ⟨c, hc, h⟩ := exists_ge_pow_inf_eq_pow_smul I N 1
  exact ⟨c, hc, h⟩

end Ideal
