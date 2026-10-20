/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ComplexShapeSigns
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor signs for integer chain degrees

The downward complex shape on `ℤ` carries the usual Koszul sign character.  This is a property
of the indexing shape itself, so it lives below all chain-DGA and monoid constructions.
-/

@[expose] public section

namespace ComplexShape.downInt

/-- The sign character on integer chain degrees. -/
def signCharacter : Multiplicative ℤ →* ℤˣ :=
  MonoidHom.mk' Int.negOnePow Int.negOnePow_add

/-- Downward adjacency is preserved by addition on the right. -/
theorem rel_add (p q r : ℤ) (hpq : (ComplexShape.down ℤ).Rel p q) :
    (ComplexShape.down ℤ).Rel (p + r) (q + r) := sorry

/-- Downward adjacency is preserved by addition on the left. -/
theorem add_rel (p q r : ℤ) (hpq : (ComplexShape.down ℤ).Rel p q) :
    (ComplexShape.down ℤ).Rel (r + p) (r + q) := sorry

/-- The integer chain sign changes across one downward differential. -/
theorem signCharacter_succ (p q : ℤ) (hpq : (ComplexShape.down ℤ).Rel p q) :
    signCharacter q = -signCharacter p := sorry

/-- Integer-indexed chain complexes carry the standard Koszul tensor signs. -/
@[stacks 0GZ4 "integer chain tensor signs"]
instance tensorSigns : (ComplexShape.down ℤ).TensorSigns where
  ε' := signCharacter
  rel_add := rel_add
  add_rel := add_rel
  ε'_succ := signCharacter_succ

/-- The tensor sign in integer chain degree `n` is `n.negOnePow`. -/
@[simp]
theorem epsilon_apply (n : ℤ) :
    (ComplexShape.down ℤ).ε n = n.negOnePow := sorry

end ComplexShape.downInt

#synth (ComplexShape.down ℤ).TensorSigns

