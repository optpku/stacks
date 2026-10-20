/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ComposableArrows.IntFamily
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Vanishing.Finite

@[expose] public section

/-!
# Shifted-Hom Vanishing for Finite Composable Rows

This leaf expresses displaced-diagonal vanishing of finite rows directly in
their canonical finite coordinates.
-/

universe v u

namespace CategoryTheory.ComposableArrows.IntFamily

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ]

/-- Displaced-diagonal vanishing of two finite rows is equivalent to its finite-coordinate
family of shifted-Hom conditions. -/
@[stacks 0DW1]
theorem vanishesAbove_iff {n : ℕ} {r : ℤ} {X X' : ComposableArrows D n} :
    ShiftedHom.vanishesAbove r X.intFamily X'.intFamily ↔
      ∀ ⦃a b : Fin (n + 1)⦄, (a.1 : ℤ) + r < b.1 →
        Subsingleton (ShiftedHom (X.obj a) (X'.obj b) ((a.1 : ℤ) + r - b.1)) := sorry

/-- Displaced-diagonal vanishing of finite rows gives the corresponding shifted-Hom
subsingleton at any pair of finite coordinates. -/
@[stacks 0DW1]
theorem subsingleton {n : ℕ} {r : ℤ} {X X' : ComposableArrows D n}
    (h : ShiftedHom.vanishesAbove r X.intFamily X'.intFamily)
    {a b : Fin (n + 1)} (hab : (a.1 : ℤ) + r < b.1) :
    Subsingleton (ShiftedHom (X.obj a) (X'.obj b) ((a.1 : ℤ) + r - b.1)) := sorry

end CategoryTheory.ComposableArrows.IntFamily
