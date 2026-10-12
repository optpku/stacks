/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Extended natural cardinalities of sets

This file supplies small proposition-level bridges around `Set.encard` that are useful when a
mathematical statement is phrased by existence and uniqueness rather than singleton equality.
@stack 0C37
-/

@[expose] public section

universe u

namespace Set

variable {α : Type u}

/-- A set has extended cardinality one exactly when it has a unique element. -/
@[stacks 0C37 "extended cardinality one and unique membership"]
theorem encard_eq_one_iff_existsUnique_mem (s : Set α) :
    s.encard = 1 ↔ ∃! x, x ∈ s := by
  rw [encard_eq_one]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, mem_singleton x, fun y hy ↦ mem_singleton_iff.mp hy⟩
  · rintro ⟨x, hx, hunique⟩
    refine ⟨x, Subset.antisymm ?_ (singleton_subset_iff.mpr hx)⟩
    intro y hy
    exact mem_singleton_iff.mpr (hunique y hy)

end Set
