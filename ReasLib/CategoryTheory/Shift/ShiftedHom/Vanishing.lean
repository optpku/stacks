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
# Banded Vanishing of Shifted Morphisms

This leaf owns the elementary diagonal vanishing conditions on two
integer-indexed families of objects.  It does not depend on finite rows or on
triangulated structure.
-/

namespace CategoryTheory

namespace ShiftedHom

universe v u

section

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]

/-- Shifted morphisms from `X i` to `X' j` vanish above the diagonal displaced by `r`. -/
def vanishesAbove (r : ℤ) (X X' : ℤ → D) : Prop :=
  ∀ ⦃i j : ℤ⦄, i > j + r → Subsingleton (ShiftedHom (X i) (X' j) (j + r - i))

/-- Extract shifted-Hom subsingletonness at a pair of indices above the displaced diagonal. -/
@[stacks 0DW1]
theorem vanishesAbove.subsingleton {r i j : ℤ} {X X' : ℤ → D}
    (h : vanishesAbove r X X') (hij : j + r < i) :
    Subsingleton (ShiftedHom (X i) (X' j) (j + r - i)) := sorry

/-- Translating the source and target indices changes the diagonal displacement by their
relative translation. -/
@[stacks 0DW1]
theorem vanishesAbove.translate {r : ℤ} {X X' : ℤ → D}
    (h : vanishesAbove r X X') (a b : ℤ) :
    vanishesAbove (b + r - a) (fun i ↦ X (i + a)) (fun j ↦ X' (j + b)) := sorry

/-- Translating both index families identifies displaced-diagonal vanishing with the original
condition after adjusting the displacement by the relative translation. -/
@[stacks 0DW1]
theorem vanishesAbove.translate_iff {r : ℤ} {X X' : ℤ → D} (a b : ℤ) :
    vanishesAbove (b + r - a) (fun i ↦ X (i + a)) (fun j ↦ X' (j + b)) ↔
      vanishesAbove r X X' := sorry

/-- Stacks 0DW1: shifted morphisms vanish above the successor diagonal. -/
@[stacks 0DW1]
def vanishesAboveSuccessor (X X' : ℤ → D) : Prop :=
  vanishesAbove (1 : ℤ) X X'

end

end ShiftedHom

end CategoryTheory
