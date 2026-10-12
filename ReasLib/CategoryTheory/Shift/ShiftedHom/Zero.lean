/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Shifted Morphisms From and Into Zero Objects

This file records the elementary subsingleton consequences of either endpoint
of a shifted morphism being a zero object.
-/

universe v u

namespace CategoryTheory.ShiftedHom

variable {C : Type u} [Category.{v} C]

section AddMonoid

variable {M : Type*} [AddMonoid M] [HasShift C M]

/-- Shifted morphisms with a zero source form a subsingleton. -/
@[stacks 0DW1]
theorem subsingleton_of_isZero_src {X Y : C} (hX : Limits.IsZero X) (n : M) :
    Subsingleton (ShiftedHom X Y n) := sorry

end AddMonoid

section AddGroup

variable {M : Type*} [AddGroup M] [HasShift C M]

/-- Shifted morphisms with a zero target form a subsingleton. -/
@[stacks 0DW1]
theorem subsingleton_of_isZero_tgt {X Y : C} (hY : Limits.IsZero Y) (n : M) :
    Subsingleton (ShiftedHom X Y n) := sorry

end AddGroup

end CategoryTheory.ShiftedHom
