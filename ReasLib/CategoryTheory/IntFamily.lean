/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Integer-Indexed Views of Finite Families

This leaf extends a finite family of objects by the zero object to an
integer-indexed family, using the reverse of the standard `Fin (n + 1)`
ordering. It is independent of arrows, complexes, and triangulated structure.
-/

open scoped ZeroObject

universe v u

namespace CategoryTheory

namespace IntFamily

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D]
variable {n : ℕ}

/-- Stacks 0DW1: extend a finite family of objects by zero to an integer-indexed family, with the
finite ordering reversed. -/
@[stacks 0DW1]
noncomputable def reverseOfFin (X : Fin (n + 1) → D) : ℤ → D := fun k ↦
  if 0 ≤ k ∧ k ≤ n then
    X (Fin.rev (Fin.ofNat (n + 1) k.toNat))
  else
    0

/-- On a nonnegative finite index, `reverseOfFin` evaluates the original family at the reversed
`Fin` index. -/
@[stacks 0DW1, simp]
theorem reverseOfFin_natCast (X : Fin (n + 1) → D) (a : Fin (n + 1)) :
    reverseOfFin X (a.1 : ℤ) = X a.rev := sorry

/-- On its integer support, `reverseOfFin` is given by the reversed finite index. -/
@[stacks 0DW1, simp]
theorem reverseOfFin_apply_of_nonneg_of_le (X : Fin (n + 1) → D) {k : ℤ}
    (h₀ : 0 ≤ k) (hₙ : k ≤ n) :
    reverseOfFin X k = X (Fin.rev (Fin.ofNat (n + 1) k.toNat)) := sorry

/-- Evaluating `reverseOfFin` on a supported index recovers the original finite family. -/
@[stacks 0DW1, simp]
theorem reverseOfFin_apply (X : Fin (n + 1) → D) (a : Fin (n + 1)) :
    reverseOfFin X (((n - a.1 : ℕ) : ℤ)) = X a := sorry

/-- `reverseOfFin` is the zero object at negative indices. -/
@[stacks 0DW1, simp]
theorem reverseOfFin_eq_zero_of_neg (X : Fin (n + 1) → D) {k : ℤ} (hk : k < 0) :
    reverseOfFin X k = 0 := sorry

/-- `reverseOfFin` is the zero object above its finite support. -/
@[stacks 0DW1, simp]
theorem reverseOfFin_eq_zero_of_natCast_lt
    (X : Fin (n + 1) → D) {k : ℤ} (hk : (n : ℤ) < k) :
    reverseOfFin X k = 0 := sorry

end

end IntFamily

end CategoryTheory
