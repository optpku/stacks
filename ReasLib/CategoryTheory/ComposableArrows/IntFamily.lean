/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.IntFamily
public import Mathlib.CategoryTheory.ComposableArrows.Basic

@[expose] public section

/-!
# Integer-Indexed Views of Finite Composable Rows

This leaf equips a finite row with its reversed integer-indexed extension by
zero. It is independent of complexes and triangulated structure.
-/

universe v u

namespace CategoryTheory.ComposableArrows

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D]
variable {n : ℕ}

/-- Stacks 0DW1: the reversed integer-indexed extension by zero of a finite row. -/
@[stacks 0DW1]
noncomputable def intFamily (X : ComposableArrows D n) : ℤ → D :=
  CategoryTheory.IntFamily.reverseOfFin X.obj

/-- The integer-indexed view recovers every object of a finite row on its supported indices. -/
@[simp, stacks 0DW1]
theorem intFamily_reverse (X : ComposableArrows D n) (a : Fin (n + 1)) :
    X.intFamily (((n - a.1 : ℕ) : ℤ)) = X.obj a := sorry

end CategoryTheory.ComposableArrows
