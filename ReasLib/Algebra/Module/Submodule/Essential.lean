/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Submodule.Lattice

@[expose] public section

universe u v

/-- A submodule meets every nonzero submodule nontrivially if and only if every
nonzero element has a nonzero scalar multiple in the submodule. -/
theorem Submodule.essential_iff_exists_smul_mem
    {R : Type u} {N : Type v} [CommRing R] [AddCommGroup N] [Module R N]
    (M : Submodule R N) :
    (∀ P : Submodule R N, P ≠ ⊥ → M ⊓ P ≠ ⊥) ↔
      ∀ x : N, x ≠ 0 → ∃ r : R, r • x ∈ M ∧ r • x ≠ 0 := sorry
