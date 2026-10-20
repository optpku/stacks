module

public import ReasLib.CategoryTheory.IntFamily
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Zero
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Vanishing
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Shifted-Hom Vanishing for Finite Families

This leaf transfers displaced-diagonal vanishing from the integer extension of
two finite families back to their canonical `Fin` coordinates.
-/

universe v u

namespace CategoryTheory.ShiftedHom

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ]

/-- Displaced-diagonal vanishing for reversed zero-extended finite families is equivalent to the
corresponding finite collection of shifted-Hom subsingleton conditions. -/
@[stacks 0DW1]
theorem vanishesAbove.reverseOfFin_iff
    {n : ℕ} {r : ℤ} {X X' : Fin (n + 1) → D} :
    vanishesAbove r (IntFamily.reverseOfFin X) (IntFamily.reverseOfFin X') ↔
      ∀ ⦃a b : Fin (n + 1)⦄, (a.1 : ℤ) + r < b.1 →
        Subsingleton (ShiftedHom (X a) (X' b) ((a.1 : ℤ) + r - b.1)) := sorry

/-- Displaced-diagonal vanishing of reversed integer extensions specializes to the corresponding
shifted Hom between members of the finite families. -/
@[stacks 0DW1]
theorem vanishesAbove.subsingleton_reverseOfFin
    {n : ℕ} {r : ℤ} {X X' : Fin (n + 1) → D}
    (h : vanishesAbove r (IntFamily.reverseOfFin X) (IntFamily.reverseOfFin X'))
    {a b : Fin (n + 1)} (hab : (a.1 : ℤ) + r < b.1) :
    Subsingleton (ShiftedHom (X a) (X' b) ((a.1 : ℤ) + r - b.1)) := sorry

end CategoryTheory.ShiftedHom
